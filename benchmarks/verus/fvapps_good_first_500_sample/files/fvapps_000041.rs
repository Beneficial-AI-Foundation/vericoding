// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve_bracket_sequence(n: usize, k: usize, s: Vec<char>) -> (result: Vec<Vec<usize>>)
    requires 
        n >= 2,
        n % 2 == 0,
        k >= 1,
        k <= n / 2,
        s.len() == n,
        forall|i: int| 0 <= i < s.len() ==> (s[i] == '(' || s[i] == ')'),
    ensures
        result.len() <= n,
        forall|i: int| 0 <= i < result.len() ==> (
            result[i].len() == 2 &&
            result[i][0] >= 1 &&
            result[i][1] <= n &&
            result[i][0] <= result[i][1]
        ),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}