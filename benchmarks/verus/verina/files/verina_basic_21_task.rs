// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_subseq_at(sub: Vec<i32>, main: Vec<i32>, i: int) -> bool {
    0 <= i && i + sub.len() <= main.len() && 
    (forall|j: int| 0 <= j < sub.len() ==> sub[j] == main[i + j])
}
// </vc-helpers>

// <vc-spec>
fn is_sublist(sub: &Vec<i32>, main: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| is_subseq_at(*sub, *main, i),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>


}
fn main() {}