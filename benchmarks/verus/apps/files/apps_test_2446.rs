// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn gcd(a: int, b: int) -> int
    requires a > 0 && b > 0
    ensures gcd(a, b) > 0
    decreases a + b
{
    if a == b {
        a
    } else if a > b {
        gcd(a - b, b)
    } else {
        gcd(a, b - a)
    }
}

spec fn split_lines_helper(s: Seq<char>, index: int, current: Seq<char>, acc: Seq<Seq<char>>) -> Seq<Seq<char>>
    decreases s.len() - index
{
    if index >= s.len() {
        acc.push(current)
    } else {
        split_lines_helper(s, index + 1, current, acc)
    }
}

spec fn parse_int_helper(s: Seq<char>, index: int, acc: int) -> int
    decreases s.len() - index
{
    if index >= s.len() {
        acc
    } else {
        parse_int_helper(s, index + 1, acc)
    }
}

spec fn parse_int_array_helper(s: Seq<char>, index: int, current: Seq<char>, acc: Seq<int>) -> Seq<int>
    decreases s.len() - index
{
    if index >= s.len() {
        acc.push(parse_int_helper(current, 0, 0))
    } else {
        parse_int_array_helper(s, index + 1, current, acc)
    }
}

spec fn int_to_string_helper(n: int, acc: Seq<char>) -> Seq<char>
    decreases n
{
    if n == 0 {
        acc
    } else {
        int_to_string_helper(n / 10, acc)
    }
}

spec fn valid_input(input: Seq<char>) -> bool {
    let lines = split_lines_func(input);
    lines.len() >= 3 &&
    parse_int_func(lines[0]) > 0 &&
    parse_int_func(lines[2]) >= 0 &&
    lines.len() >= 3 + parse_int_func(lines[2]) &&
    parse_int_array_func(lines[1]).len() == parse_int_func(lines[0]) &&
    (forall|i: int| 0 <= i < parse_int_array_func(lines[1]).len() ==> parse_int_array_func(lines[1])[i] > 0) &&
    forall|i: int| 0 <= i < parse_int_func(lines[2]) ==> parse_int_func(lines[3 + i]) > 0
}

spec fn get_expected_results(input: Seq<char>) -> Seq<int> {
    let lines = split_lines_func(input);
    let arr = parse_int_array_func(lines[1]);
    let q = parse_int_func(lines[2]);
    Seq::new(q as nat, |i: int| count_subarrays_with_gcd(arr, parse_int_func(lines[3 + i])))
}

spec fn format_output(results: Seq<int>) -> Seq<char> {
    if results.len() == 0 {
        Seq::empty()
    } else if results.len() == 1 {
        int_to_string_func(results[0])
    } else {
        int_to_string_func(results[0]) + seq!['\n'] + format_output(results.subrange(1, results.len() as int))
    }
}

spec fn count_subarrays_with_gcd(arr: Seq<int>, target: int) -> int {
    subarray_pairs(arr).filter(|pair: (int, int)| subarray_gcd(arr, pair.0, pair.1) == target).len() as int
}

spec fn subarray_pairs(arr: Seq<int>) -> Set<(int, int)> {
    Set::new(|pair: (int, int)| 0 <= pair.0 <= pair.1 < arr.len())
}

spec fn subarray_gcd(arr: Seq<int>, start: int, end: int) -> int
    decreases end - start
{
    if start == end {
        arr[start]
    } else {
        let rest = subarray_gcd(arr, start + 1, end);
        gcd(arr[start], rest)
    }
}

spec fn split_lines_func(s: Seq<char>) -> Seq<Seq<char>> {
    split_lines_helper(s, 0, Seq::empty(), Seq::empty())
}

spec fn parse_int_func(s: Seq<char>) -> int {
    parse_int_helper(s, 0, 0)
}

spec fn parse_int_array_func(s: Seq<char>) -> Seq<int> {
    parse_int_array_helper(s, 0, Seq::empty(), Seq::empty())
}

spec fn int_to_string_func(n: int) -> Seq<char> {
    if n == 0 {
        seq!['0']
    } else {
        int_to_string_helper(n, Seq::empty())
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
  requires
      input.len() > 0,
      valid_input(input@),
  ensures
      result@ == format_output(get_expected_results(input@)),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}