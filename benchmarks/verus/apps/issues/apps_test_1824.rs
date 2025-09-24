// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    let lines = split_by_newline(input);
    lines.len() >= 4 && 
    is_valid_integer(lines[0]) &&
    string_to_int(lines[0]) >= 3 &&
    split_by_space(lines[1]).len() == string_to_int(lines[0]) &&
    split_by_space(lines[2]).len() == string_to_int(lines[0]) - 1 &&
    split_by_space(lines[3]).len() == string_to_int(lines[0]) - 2 &&
    (forall|i: int| 0 <= i < split_by_space(lines[1]).len() ==> is_valid_integer(split_by_space(lines[1])[i])) &&
    (forall|i: int| 0 <= i < split_by_space(lines[2]).len() ==> is_valid_integer(split_by_space(lines[2])[i])) &&
    (forall|i: int| 0 <= i < split_by_space(lines[3]).len() ==> is_valid_integer(split_by_space(lines[3])[i]))
}

spec fn is_valid_integer(s: Seq<char>) -> bool {
    s.len() > 0 && (s[0] == '-' ==> s.len() > 1) && 
    (forall|i: int| (if s[0] == '-' { 1int } else { 0int }) <= i < s.len() ==> '0' <= s[i] <= '9')
}

spec fn get_first_sum(input: Seq<char>) -> int {
    let lines = split_by_newline(input);
    let first_line = split_by_space(lines[1]);
    sum_sequence(first_line)
}

spec fn get_second_sum(input: Seq<char>) -> int {
    let lines = split_by_newline(input);
    let second_line = split_by_space(lines[2]);
    sum_sequence(second_line)
}

spec fn get_third_sum(input: Seq<char>) -> int {
    let lines = split_by_newline(input);
    let third_line = split_by_space(lines[3]);
    sum_sequence(third_line)
}

spec fn sum_sequence(numbers: Seq<Seq<char>>) -> int
    decreases numbers.len()
{
    if numbers.len() == 0 { 0 }
    else { string_to_int(numbers[0]) + sum_sequence(numbers.drop_first()) }
}

spec fn split_by_newline(s: Seq<char>) -> Seq<Seq<char>>
    decreases s.len()
{
    if s.len() == 0 { seq![] }
    else if s[0] == '\n' { split_by_newline(s.drop_first()) }
    else {
        let rest = split_by_newline(s.drop_first());
        if rest.len() == 0 { seq![s] }
        else { seq![seq![s[0]].add(rest[0])].add(rest.drop_first()) }
    }
}

spec fn split_by_space(s: Seq<char>) -> Seq<Seq<char>> {
    split_by_char(s, ' ')
}

spec fn split_by_char(s: Seq<char>, delimiter: char) -> Seq<Seq<char>>
    decreases s.len()
{
    if s.len() == 0 { seq![] }
    else {
        let pos = find_char(s, delimiter, 0);
        if pos == -1 { seq![s] }
        else if pos == 0 { split_by_char(s.drop_first(), delimiter) }
        else { seq![s.take(pos)].add(split_by_char(s.skip(pos + 1), delimiter)) }
    }
}

spec fn find_char(s: Seq<char>, c: char, start: int) -> int
    decreases s.len() - start
{
    if start >= s.len() { -1 }
    else if s[start] == c { start }
    else { find_char(s, c, start + 1) }
}

spec fn string_to_int(s: Seq<char>) -> int {
    if s.len() == 0 { 0 }
    else if s[0] == '-' { -string_to_int_helper(s.drop_first(), 0) }
    else { string_to_int_helper(s, 0) }
}

spec fn string_to_int_helper(s: Seq<char>, acc: int) -> int
    decreases s.len()
{
    if s.len() == 0 { acc }
    else if '0' <= s[0] <= '9' {
        string_to_int_helper(s.drop_first(), acc * 10 + (s[0] as int - '0' as int))
    } else { acc }
}

spec fn int_to_string(n: int) -> Seq<char> {
    if n == 0 { seq!['0'] }
    else if n < 0 { seq!['-'].add(int_to_string_helper(-n)) }
    else { int_to_string_helper(n) }
}

spec fn int_to_string_helper(n: int) -> Seq<char>
    decreases n
{
    if n == 0 { seq![] }
    else { int_to_string_helper(n / 10).add(seq![((n % 10) + '0' as int) as char]) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires input.len() > 0
    requires valid_input(input@)
    ensures result@ == int_to_string(get_first_sum(input@) - get_second_sum(input@)).add(seq!['\n']).add(int_to_string(get_second_sum(input@) - get_third_sum(input@))).add(seq!['\n'])
// </vc-spec>
// <vc-code>
{
    assume(false);
    String::new()
}
// </vc-code>


}

fn main() {}