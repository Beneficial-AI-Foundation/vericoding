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
fn reverse_string(s: Seq<char>) -> Seq<char>
    ensures reverse_string(s) == if s.len() == 0 { s } else { reverse_string(s.subrange(1, s.len() as int)).push(s.index(0)) }
{
    if s.len() == 0 {
        seq![]
    } else {
        reverse_string(s.subrange(1, s.len() as int)).push(s.index(0))
    }
}

proof fn lexicographically_le(s1: Seq<char>, s2: Seq<char>) -> bool
    ensures lexicographically_le(s1, s2) == (s1 == seq![] || (s2 != seq![] && s1.index(0) <= s2.index(0) && lexicographically_le(s1.subrange(1, s1.len() as int), s2.subrange(1, s2.len() as int))))
{
    if s1.len() == 0 || s2.len() == 0 {
        s1.len() == 0
    } else {
        s1.index(0) <= s2.index(0) && lexicographically_le(s1.subrange(1, s1.len() as int), s2.subrange(1, s2.len() as int))
    }
}

fn parse_input_line(line: &str) -> (n: int, k: int, input_str: Seq<char>)
    requires line@.len() >= 1 && is_lowercase_letter(line@.last())
    ensures 1 <= k <= n && input_str.len() == n
{
    let parts = line.split(' ');
    let n_str = parts.next().unwrap();
    let k_str = parts.next().unwrap();
    let s_str = parts.next().unwrap();
    let n_val = n_str.parse::<usize>().unwrap() as int;
    let k_val = k_str.parse::<usize>().unwrap() as int;
    (n_val, k_val, s_str.chars().collect::<Vec<_>>()@)
}
// </vc-helpers>

// <vc-spec>
fn solve(s: &str) -> (result: String)
  requires valid_input(s@)
  ensures valid_output(result@)
// </vc-spec>
// <vc-code>
{
    let mut lines = s.lines();
    let t_line = lines.next().unwrap();
    let t = t_line.parse::<usize>().unwrap();
    
    let mut result_vec = Vec::new();
    
    for _ in 0..t {
        let line = lines.next().unwrap();
        let (n, k, input_str) = parse_input_line(line);
        
        let mut best_k = 1;
        let mut best_result = transform_string(input_str, n, 1);
        
        for candidate_k in 2..=n {
            let candidate_result = transform_string(input_str, n, candidate_k);
            if lexicographically_le(candidate_result, best_result) {
                best_k = candidate_k;
                best_result = candidate_result;
            }
        }
        
        let mut result_line = format!("{} {}\n", best_k, best_result.to_string());
        result_vec.push(result_line);
    }
    
    result_vec.join("")
}
// </vc-code>


}

fn main() {}