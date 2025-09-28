// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0
}

spec fn get_max_simultaneous_arrivals(input: Seq<char>) -> int {
    let lines = split_lines_function(input);
    if lines.len() == 0 { 0 } else { max_frequency_in_all_lines(lines) }
}

spec fn split_lines_function(s: Seq<char>) -> Seq<Seq<char>> {
    split_lines_helper(s, 0, 0, seq![])
}

spec fn split_lines_helper(s: Seq<char>, start: int, i: int, acc: Seq<Seq<char>>) -> Seq<Seq<char>>
    decreases s.len() - i
{
    if i >= s.len() {
        if start < s.len() { acc.push(s.subrange(start, s.len() as int)) } else { acc }
    } else if s[i] == '\n' {
        let new_acc = if start < i { acc.push(s.subrange(start, i)) } else { acc };
        split_lines_helper(s, i + 1, i + 1, new_acc)
    } else {
        split_lines_helper(s, start, i + 1, acc)
    }
}

spec fn max_frequency_in_all_lines(lines: Seq<Seq<char>>) -> int {
    if lines.len() == 0 { 0 } else { max_frequency_helper(lines, 0, 0) }
}

spec fn max_frequency_helper(lines: Seq<Seq<char>>, index: int, current_max: int) -> int
    decreases lines.len() - index
{
    if index >= lines.len() { current_max }
    else {
        let count = count_occurrences(lines, lines[index]);
        let new_max = if count > current_max { count } else { current_max };
        max_frequency_helper(lines, index + 1, new_max)
    }
}

spec fn count_occurrences(lines: Seq<Seq<char>>, target: Seq<char>) -> int {
    count_occurrences_helper(lines, target, 0, 0)
}

spec fn count_occurrences_helper(lines: Seq<Seq<char>>, target: Seq<char>, index: int, count: int) -> int
    decreases lines.len() - index
{
    if index >= lines.len() { count }
    else {
        let new_count = if lines[index] == target { count + 1 } else { count };
        count_occurrences_helper(lines, target, index + 1, new_count)
    }
}

spec fn skip_identical(lines: Seq<Seq<char>>, index: int) -> int
    decreases lines.len() - index
{
    if index + 1 >= lines.len() { lines.len() as int }
    else if lines[index + 1] == lines[index] { skip_identical(lines, index + 1) }
    else { index + 1 }
}

spec fn int_to_string_function(n: int) -> Seq<char> {
    if n == 0 { seq!['0'] }
    else if n > 0 { int_to_string_helper(n, seq![]) }
    else { seq!['0'] }
}

spec fn int_to_string_helper(n: int, acc: Seq<char>) -> Seq<char>
    decreases n
{
    let digit = n % 10;
    let digit_char = ('0' as u32 + digit as u32) as char;
    if n / 10 == 0 { seq![digit_char].add(acc) }
    else if n / 10 > 0 && n / 10 < n { int_to_string_helper(n / 10, seq![digit_char].add(acc)) }
    else { seq![digit_char].add(acc) }
}
// </vc-preamble>

// <vc-helpers>
fn make_nonempty_vec() -> (v: Vec<char>)
    ensures
        v@.len() > 0,
{
    let mut v = Vec::<char>::new();
    v.push('0');
    v
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures result@.len() > 0
// </vc-spec>
// <vc-code>
{
    let v = make_nonempty_vec();
    v
}
// </vc-code>


}

fn main() {}