// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn int_to_string(n: int) -> Seq<char> {
    if n == 0 { seq!['0'] }
    else if n == 1 { seq!['1'] }
    else if n == 2 { seq!['2'] }
    else if n == 3 { seq!['3'] }
    else if n == 4 { seq!['4'] }
    else if n == 5 { seq!['5'] }
    else if n == 6 { seq!['6'] }
    else if n == 7 { seq!['7'] }
    else if n == 8 { seq!['8'] }
    else if n == 9 { seq!['9'] }
    else if n == 10 { seq!['1', '0'] }
    else if n == 11 { seq!['1', '1'] }
    else if n == 12 { seq!['1', '2'] }
    else if n == 13 { seq!['1', '3'] }
    else if n == 14 { seq!['1', '4'] }
    else if n == 15 { seq!['1', '5'] }
    else if n == 16 { seq!['1', '6'] }
    else if n == 17 { seq!['1', '7'] }
    else if n == 18 { seq!['1', '8'] }
    else if n == 19 { seq!['1', '9'] }
    else if n == 20 { seq!['2', '0'] }
    else if n == 21 { seq!['2', '1'] }
    else if n == 22 { seq!['2', '2'] }
    else if n == 23 { seq!['2', '3'] }
    else { seq!['0'] }
}

spec fn valid_input(input: Seq<char>) -> bool {
    exists|a: int, b: int| 0 <= a <= 23 && 0 <= b <= 23 && 
    (input == int_to_string(a) + seq![' '] + int_to_string(b) + seq!['\n'] ||
     input == int_to_string(a) + seq![' '] + int_to_string(b))
}

spec fn contest_start_time(a: int, b: int) -> int {
    (a + b) % 24
}

spec fn correct_output(input: Seq<char>, result: Seq<char>) -> bool {
    valid_input(input) ==> 
    exists|a: int, b: int| 0 <= a <= 23 && 0 <= b <= 23 && 
    (input == int_to_string(a) + seq![' '] + int_to_string(b) + seq!['\n'] ||
     input == int_to_string(a) + seq![' '] + int_to_string(b)) &&
    result == int_to_string(contest_start_time(a, b)) + seq!['\n']
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed compilation error by resolving `string_to_ascii_chars_lib` import and casting `n` to `u32` for `nat_to_string_n_digits_max`. */
use vstd::seq::*;
use vstd::string::*;

spec fn parse_int_from_seq_char(s: Seq<char>) -> (i: int)
    decreases s.len()
{
    if s.len() == 0 { 0int }
    else if s.len() == 1 {
        if s[0] == '0' { 0int }
        else if s[0] == '1' { 1int }
        else if s[0] == '2' { 2int }
        else if s[0] == '3' { 3int }
        else if s[0] == '4' { 4int }
        else if s[0] == '5' { 5int }
        else if s[0] == '6' { 6int }
        else if s[0] == '7' { 7int }
        else if s[0] == '8' { 8int }
        else if s[0] == '9' { 9int }
        else { 0int } // Should not happen with valid input specs
    } else {
        let first_digit_val = if s[0] == '0' { 0int }
        else if s[0] == '1' { 1int }
        else if s[0] == '2' { 2int }
        else if s[0] == '3' { 3int }
        else if s[0] == '4' { 4int }
        else if s[0] == '5' { 5int }
        else if s[0] == '6' { 6int }
        else if s[0] == '7' { 7int }
        else if s[0] == '8' { 8int }
        else if s[0] == '9' { 9int }
        else { 0int };
        first_digit_val * 10 + parse_int_from_seq_char(s.subsequence(1, s.len()))
    }
}

spec fn find_first_separator(s: Seq<char>, start_index: int) -> int
    requires
        0 <= start_index <= s.len(),
    decreases s.len() - start_index
{
    if start_index >= s.len() { s.len() as int }
    else if (start_index as nat) < s.len() && (s[start_index as nat] == ' ' || s[start_index as nat] == '\n') { start_index }
    else { find_first_separator(s, start_index + 1) }
}

fn int_to_string_exec(n: int) -> (s: String)
    requires
        0 <= n <= 23,
    ensures
        s@ == int_to_string(n),
{
    // `nat_to_string_n_digits_max` expects `u32` for the number, not `nat`
    vstd::string::nat_to_string_n_digits_max(n as u32, 2)
}
// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (result: String)
    ensures correct_output(input@, result@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type casting for `second_num_start_idx` to allow indexing `input_seq` with `as usize`. */
{
    proof {
        assert(input.len() >= 3);
    }
    
    let input_seq = input@;

    let space_idx = find_first_separator(input_seq, 0);

    let first_num_seq = input_seq.subsequence(0, space_idx);
    let a = parse_int_from_seq_char(first_num_seq);

    // Correctly handle the type of `second_num_start_idx` to allow indexing input_seq
    let second_num_start_idx: usize = if (space_idx as usize) < input_seq.len() && input_seq[space_idx as usize] == ' ' { (space_idx + 1) as usize } else { space_idx as usize };
    let end_idx = find_first_separator(input_seq, second_num_start_idx as int);
    let second_num_seq = input_seq.subsequence(second_num_start_idx as int, end_idx);
    let b = parse_int_from_seq_char(second_num_seq);
    
    let start_time = contest_start_time(a, b);

    let result_string = int_to_string_exec(start_time);
    String::from_str_literal("") + result_string + String::from_str_literal("\n")
}
// </vc-code>


}

fn main() {}