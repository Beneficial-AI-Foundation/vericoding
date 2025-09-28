// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 2 &&
    (s.last() == '\n' || (s.len() >= 2 && s.subrange(s.len() - 2, s.len() as int) == seq!['\n']))
}

spec fn valid_output(result: Seq<char>) -> bool {
    result.len() >= 0 &&
    (result.len() == 0 || result.last() == '\n')
}

spec fn transform_string(input_str: Seq<char>, n: int, k: int) -> Seq<char>
    recommends 1 <= k <= n && input_str.len() == n
{
    let i = k - 1;
    if (n - i) % 2 == 0 {
        input_str.subrange(i, n as int) + input_str.subrange(0, i)
    } else {
        input_str.subrange(i, n as int) + reverse_string(input_str.subrange(0, i))
    }
}

spec fn is_lexicographically_optimal(result_str: Seq<char>, input_str: Seq<char>, n: int, k: int) -> bool
    recommends input_str.len() == n
{
    1 <= k <= n &&
    result_str == transform_string(input_str, n, k) &&
    true /* Simplified to avoid trigger issues */
}

spec fn split_lines(s: Seq<char>) -> Seq<Seq<char>> {
    seq![] /* TODO: Define line splitting logic */
}

spec fn parse_int(line: Seq<char>) -> int {
    0 /* TODO: Define integer parsing logic */
}

spec fn is_lowercase_letter(c: char) -> bool {
    'a' <= c && c <= 'z'
}

spec fn reverse_string(s: Seq<char>) -> Seq<char> {
    s /* TODO: Define string reversal logic */
}

spec fn lexicographically_le(s1: Seq<char>, s2: Seq<char>) -> bool {
    true /* TODO: Define lexicographic comparison */
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Avoided shadowing of 'result' in postconditions by not declaring local 'result' variables */
fn exec_split_lines(s: &str) -> Vec<String>
{
    s.split('\n').map(|x| x.to_string()).collect()
}

fn exec_parse_int(line: &str) -> i64
    requires
        line@.len() > 0,
        forall |i:int| 0 <= i < line@.len() ==> '0' <= line@[i] <= '9'
    ensures
        result >= 0
{
    let mut parsed: i64 = 0;
    for c in line.chars()
    
        invariant
            parsed >= 0
    
    {
        parsed = parsed * 10 + ((c as u32 as i64) - ('0' as u32 as i64));
    }
    parsed
}

fn exec_reverse_string(s: String) -> String
{
    s.chars().rev().collect()
}

fn exec_lexicographically_le(s1: &str, s2: &str) -> bool
{
    s1 <= s2
}

fn exec_transform_string(input_str: String, n: usize, k: usize) -> String
    requires
        input_str@.len() == n as int,
        1 <= k <= n
    ensures
        result@.len() == n as int
{
    let i = k - 1;
    let i_usize = i;
    let n_usize = n;
    let left = &input_str[i_usize..n_usize];
    let right = &input_str[0..i_usize];
    if (n - i) % 2 == 0 {
        left.to_string() + right
    } else {
        left.to_string() + &exec_reverse_string(right.to_string())
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: &str) -> (result: String)
  requires valid_input(s@)
  ensures valid_output(result@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Maintained implementation with executable code using usize for indices */
{
    let lines = exec_split_lines(s);
    let num_n: u32 = exec_parse_int(&lines[0]) as u32;
    let num_k: u32 = exec_parse_int(&lines[1]) as u32;
    let orig_str = lines[2].clone();
    let mut best_result = orig_str.clone();
    let mut k_current: u32 = 1;
    while k_current <= num_n
        invariant
            1 <= k_current <= num_n + 1,
            best_result@.len() == num_n as int
        decreases
            num_n - k_current
    {
        let candidate = exec_transform_string(orig_str.clone(), num_n as usize, k_current as usize);
        if exec_lexicographically_le(&candidate, &best_result) {
            best_result = candidate;
        }
        k_current += 1;
    }
    best_result + "\n"
}
// </vc-code>


}

fn main() {}