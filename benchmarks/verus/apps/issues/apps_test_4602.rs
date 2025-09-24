// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(s: Seq<char>) -> bool {
    let lines = split_by_newlines(s);
    lines.len() >= 3 &&
    is_positive_integer(lines[0]) &&
    is_positive_integer(lines[1]) &&
    {
        let n = string_to_int(lines[0]);
        let k = string_to_int(lines[1]);
        1 <= n <= 100 &&
        1 <= k <= 100 &&
        is_valid_x_array(lines[2], n, k)
    }
}

spec fn valid_output(result: Seq<char>) -> bool {
    result.len() >= 2 &&
    result[result.len() - 1] == '\n' &&
    is_non_negative_integer(result.subrange(0, result.len() - 1))
}

spec fn correct_solution(input: Seq<char>, output: Seq<char>) -> bool {
    valid_input(input) && valid_output(output) ==>
        {
            let lines = split_by_newlines(input);
            let n = string_to_int(lines[0]);
            let k = string_to_int(lines[1]);
            let x = parse_int_array(lines[2]);
            x.len() == n &&
            (forall|i: int| #[trigger] x[i] == x[i] && 0 <= i < n ==> 0 < x[i] < k) &&
            {
                let expected_sum = compute_min_distance(x, k);
                string_to_int(output.subrange(0, output.len() - 1)) == expected_sum
            }
        }
}

spec fn is_positive_integer(s: Seq<char>) -> bool {
    is_non_negative_integer(s) && s.len() > 0 && 
    (s.len() > 1 || s[0] != '0') && 
    string_to_int(s) > 0
}

spec fn is_non_negative_integer(s: Seq<char>) -> bool {
    s.len() > 0 && 
    forall|i: int| #[trigger] s[i] == s[i] && 0 <= i < s.len() ==> {
        let c = s[i];
        '0' <= c && c <= '9'
    }
}

spec fn is_valid_x_array(s: Seq<char>, n: int, k: int) -> bool {
    let x = parse_int_array(s);
    x.len() == n && 
    forall|i: int| #[trigger] x[i] == x[i] && 0 <= i < n ==> 0 < x[i] < k
}

spec fn compute_min_distance(x: Seq<int>, k: int) -> int {
    /* requires forall|i: int| 0 <= i < x.len() ==> 0 < x[i] < k */
    /* ensures compute_min_distance(x, k) >= 0 */
    sum_seq(Seq::new(x.len(), |i: int| 2 * min(k - x[i], x[i])))
}

spec fn split_by_newlines(s: Seq<char>) -> Seq<Seq<char>> { 
    seq![]
}

spec fn string_to_int(s: Seq<char>) -> int { 
    0
}

spec fn parse_int_array(s: Seq<char>) -> Seq<int> { 
    seq![]
}

spec fn sum_seq(seq: Seq<int>) -> int { 
    0
}

spec fn min(a: int, b: int) -> int { 
    if a <= b { a } else { b } 
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(s: &str) -> (result: String)
requires
    s@.len() > 0,
    valid_input(s@),
ensures
    result@.len() > 0,
    result@[result@.len() - 1] == '\n',
    valid_output(result@),
    correct_solution(s@, result@),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}