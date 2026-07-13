// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn print_pattern(n: usize) -> (result: Vec<Vec<char>>)
    requires n > 0,
    ensures 
        result.len() == n,
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == n,
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> (result[i][j] == '1' || result[i][j] == ' ')
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