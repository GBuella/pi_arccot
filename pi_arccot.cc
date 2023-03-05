/* vim: set filetype=cpp : */
/* vim: set noet tw=100 ts=8 sw=8 cinoptions=+4,(0,t0: */

#include <vector>
#include <limits>
#include <cstdint>
#include <charconv>
#include <string>
#include <cstdlib>
#include <iostream>
#include <algorithm>

typedef uint32_t limb_int;
typedef uint64_t limb2_int;
typedef int64_t limb2_int_signed;

static_assert(not std::numeric_limits<limb_int>::is_signed);
static_assert(not std::numeric_limits<limb2_int>::is_signed);
static_assert(sizeof(limb2_int) >= 2 * sizeof(limb_int));
static_assert(sizeof(limb2_int_signed) >= 2 * sizeof(limb_int));

constexpr size_t limb_bits = sizeof(limb_int) * 8;

constexpr uintmax_t limb_max = std::numeric_limits<limb_int>::max();
constexpr uintmax_t arg_max = (1llu << (limb_bits / 2)) - 1;
constexpr unsigned block_height = 64;
constexpr unsigned block_width = 64;

using std::vector;
using std::cout;

static vector<limb_int> accumulator;

static unsigned long precision;
static unsigned long pi_d;
static vector<limb_int> multipliers;
static vector<limb_int> args;
static vector<limb_int> arg_sq;

static std::string progname;

struct remainder_block
{
	unsigned arg_count;
	std::vector<limb_int> remainders;
};

static vector<limb_int> quotents;
static vector<remainder_block> remainder_column;
static unsigned block_digit_offset;
static unsigned block_divisor_offset;

static void
usage_and_exit(int err)
{
	((err == 0) ? cout : std::cerr) <<
	    "Usage:\n"
	    << progname << " precision d "
	    "multiplier1 arg1 multiplier2 arg2 multiplier3 arg3...\n\n"
	    "where precision the number of " << limb_bits << " bits used for calculation,\n"
	    "and the computation to done is:\n"
	    "d * (multiplier1 * arccot(arg1) + multiplier2 * arccot(arg2) + ...)\n";

	// todo explain what numbers are accepted
	std::exit(err);
}

static void read_parameters(const char **argv)
{
	if (argv[0] == nullptr or argv[1] == nullptr)
		usage_and_exit(1);
	argv++;
	precision = std::stoul(*argv);
	if (precision < 1)
		usage_and_exit(1);
	argv++;
	pi_d = std::stoul(*argv);
	if (pi_d == 0)
		usage_and_exit(1);
	argv++;
	while (*argv != nullptr) {
		auto n = std::stoul(*argv);
		if (n > limb_max)
			usage_and_exit(1);
		multipliers.push_back(n);
		argv++;
		if (*argv == nullptr)
			usage_and_exit(1);
		n = std::stoul(*argv);
		if (n > arg_max)
			usage_and_exit(1);
		args.push_back(n);
		arg_sq.push_back(n*n);
		argv++;
	}
	if (args.empty())
		usage_and_exit(1);
}

static void initialize_variables()
{
	size_t fractional_size;
	if (precision % block_width == 0)
		fractional_size = precision;
	else
		fractional_size = (precision / block_width + 1) * block_width;
	accumulator.assign(fractional_size + block_width, 0);

	quotents.assign(block_width * args.size(), 0);
	for (size_t i = 0; i < args.size(); ++i) {
		limb2_int n = args[i];
		n *= multipliers[i];
		n *= pi_d;
		quotents[(block_width - 1) * args.size() + i] = (limb_int)n;
		quotents[(block_width - 2) * args.size() + i] = (limb_int)(n >> limb_bits);
	}

	remainder_column.clear();
	block_digit_offset = 0;
	block_divisor_offset = 1;
}

static unsigned count_non_zero_quotents()
{
	for (unsigned argi = 0; argi < args.size(); ++argi) {
		auto limb = quotents.begin() + argi;
		for (unsigned offset = 0; offset < block_width; ++offset) {
			if (*limb != 0)
				return args.size() - argi;
			limb += args.size();
		}
	}
	return 0;
}

static void accumulate(limb2_int_signed delta, unsigned offset)
{
	if (delta < 0) {
		constexpr limb2_int borrow = 1llu << limb_bits;
		limb2_int d = -delta;
		while (d > accumulator[offset]) {
			limb_int d_low = d;
			d >>= limb_bits;
			if (d_low > accumulator[offset]) {
				limb2_int temp = (borrow + accumulator[offset]) - d_low;
				accumulator[offset] = temp;
				assert((temp >> limb_bits) == 0);
				d++;
			}
			else {
				accumulator[offset] -= d_low;
			}
			offset--;
		}
		accumulator[offset] -= d;
	}
	else {
		limb2_int d = delta;
		while (d != 0) {
			d += accumulator[offset];
			accumulator[offset] = d;
			d >>= limb_bits;
			offset--;
		}
	}
}

static void process_block(remainder_block& block)
{
	auto quotent = quotents.begin();
	unsigned digit_offset = block_digit_offset;
	while (quotent != quotents.end()) {
		bool addition = true;
		auto remainder = block.remainders.begin();
		auto divisor = block_divisor_offset;
		limb2_int_signed delta = 0;
		while (remainder != block.remainders.end()) {
			limb2_int sum = 0;
			for (unsigned i = 0; i < block.arg_count; ++i) {
				limb2_int n = (((limb2_int)*remainder) << limb_bits) + quotent[i];
				quotent[i] = n / arg_sq[i];
				*remainder = n % arg_sq[i];
				sum += quotent[i];
				remainder++;
			}
			sum += ((limb2_int)(*remainder)) << limb_bits;
			*remainder = sum % divisor;
			if (addition)
				delta += sum / divisor;
			else
				delta -= sum / divisor;
			addition = not addition;
			divisor += 2;
			remainder++;
		}
		accumulate(delta, digit_offset);
		digit_offset++;
		quotent += args.size();
	}
}

static void print_integer_part()
{
	std::string result;

	unsigned first_non_zero = 0;
	while (first_non_zero < block_width and accumulator[first_non_zero] == 0) {
		first_non_zero++;
	}
	while (first_non_zero < block_width) {
		result.push_back('0' + (accumulator[block_width-1] % 10));
		limb2_int n = 0;
		for (unsigned i = 0; i < block_width; ++i) {
			n += accumulator[i];
			accumulator[i] = n / 10;
			n %= 10;
			n <<= limb_bits;
		}
		while (first_non_zero < block_width and accumulator[first_non_zero] == 0)
			first_non_zero++;
	}
	if (result.empty()) {
		cout << "0";
	}
	else {
		std::reverse(result.begin(), result.end());
		cout << result;
	}
}

static void print_fractional_part()
{
	std::string result;
	unsigned first_non_zero = accumulator.size() - 1;
	while (first_non_zero > 0 and accumulator[first_non_zero] == 0)
		first_non_zero--;
	limb_int pow10 = 1;
	for (int i = 0; i < std::numeric_limits<limb_int>::digits10; i++)
		pow10 *= 10;
	unsigned long dec_digits = (accumulator.size() - block_width)
	    * std::numeric_limits<limb_int>::digits10 - 2;
	while (first_non_zero > 0 and result.size() <= dec_digits) {
		limb2_int n = 0;
		for (unsigned i = first_non_zero; i >= block_width - 1; i--) {
			n += ((limb2_int)(accumulator[i])) * pow10;
			accumulator[i] = n;
			n >>= limb_bits;
		}
		auto p = pow10 / 10;
		for (int i = 0; i < std::numeric_limits<limb_int>::digits10; i++) {
			result.push_back('0' + (accumulator[block_width-1] / p));
			accumulator[block_width-1] %= p;
			p /= 10;
		}
		accumulator[block_width-1] = 0;
		while (first_non_zero > 0 and accumulator[first_non_zero] == 0)
			first_non_zero--;
	}
	if (not result.empty())
		cout << "." << result;
}

int main(int argc, const char **argv)
{
	static const char* default_args[] = {"", "17", "4", "5", "7", "4", "68", "2", "117", nullptr};
	progname = argv[0];
	if (argv[1] == nullptr)
		read_parameters(default_args);
	else
		read_parameters(argv);
	initialize_variables();

	while (block_digit_offset < accumulator.size()) {
		unsigned next_arg_count = args.size();
		unsigned column_index = 0;
		block_divisor_offset = 1;
		do {
			if (remainder_column.size() <= column_index) {
				remainder_column.emplace_back();
				remainder_column[column_index].arg_count = next_arg_count;
				remainder_column[column_index].remainders.assign((args.size() + 1) *
										 block_height, 0);
			}
			remainder_column[column_index].arg_count =
			    std::max(remainder_column[column_index].arg_count, next_arg_count);
			process_block(remainder_column[column_index]);
			next_arg_count = count_non_zero_quotents();
			block_divisor_offset += 2 * block_height;
			column_index++;
		} while (remainder_column.size() > column_index or next_arg_count > 0);
		block_digit_offset += block_width;
	}
	print_integer_part();
	print_fractional_part();
	cout << "\n";
}
