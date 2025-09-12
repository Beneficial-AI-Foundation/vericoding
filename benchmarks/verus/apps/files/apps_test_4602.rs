// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(s: &str) -> bool {
    let lines = split_by_newlines(s);
    lines.len() >= 3 &&
    is_positive_integer(&lines[0]) &&
    is_positive_integer(&lines[1]) &&
    {
        let n = string_to_int(&lines[0]);
        let k = string_to_int(&lines[1]);
        1 <= n <= 100 &&
        1 <= k <= 100 &&
        is_valid_x_array(&lines[2], n, k)
    }
}

spec fn valid_output(result: &str) -> bool {
    result.len() >= 2 &&
    result.chars().last() == Some('\n') &&
    is_non_negative_integer(&result[..result.len()-1])
}

spec fn correct_solution(input: &str, output: &str) -> bool {
    valid_input(input) && valid_output(output) ==> {
        let lines = split_by_newlines(input);
        let n = string_to_int(&lines[0]);
        let k = string_to_int(&lines[1]);
        let x = parse_int_array(&lines[2]);
        x.len() == n &&
        (forall|i: int| 0 <= i < n ==> 0 < x[i] < k) &&
        {
            let expected_sum = compute_min_distance(&x, k);
            string_to_int(&output[..output.len()-1]) == expected_sum
        }
    }
}

spec fn is_positive_integer(s: &str) -> bool {
    is_non_negative_integer(s) && s.len() > 0 && 
    (s.len() > 1 || s.chars().nth(0) != Some('0')) && 
    string_to_int(s) > 0
}

spec fn is_non_negative_integer(s: &str) -> bool {
    s.len() > 0 && 
    forall|i: int| 0 <= i < s.len() ==> 
        '0' <= s.chars().nth(i as usize).unwrap() <= '9'
}

spec fn is_valid_x_array(s: &str, n: int, k: int) -> bool {
    let x = parse_int_array(s);
    x.len() == n && 
    forall|i: int| 0 <= i < n ==> 0 < x[i] < k
}

spec fn compute_min_distance(x: &Seq<int>, k: int) -> int
    decreases x.len()
{
    if x.len() == 0 {
        0
    } else {
        2 * spec_min(k - x[0], x[0]) + compute_min_distance(&x.subrange(1, x.len() as int), k)
    }
}

spec fn spec_min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

spec fn split_by_newlines(s: &str) -> Seq<String> {
    Seq::empty()
}

spec fn string_to_int(s: &str) -> int {
    0
}

spec fn parse_int_array(s: &str) -> Seq<int> {
    Seq::empty()
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(s: &str) -> (result: String)
    requires s.len() > 0
    requires valid_input(s)
    ensures result.len() > 0
    ensures result.chars().last() == Some('\n')
    ensures valid_output(&result)
    ensures correct_solution(s, &result)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    String::new()
    // impl-end
}
// </vc-code>


}

fn main() {}