// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn remove_element(lst: &Vec<u8>, target: u8) -> (result: Vec<u8>)
    ensures
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] as nat != target as nat,
        forall|i: int| 0 <= i < result.len() ==> 
            exists|j: int| 0 <= j < lst.len() && #[trigger] lst[j] as nat == #[trigger] result[i] as nat && lst[j] as nat != target as nat,
        forall|i: int, j: int| 0 <= i < j < lst.len() && lst[i] as nat != target as nat && lst[j] as nat != target as nat ==> 
            exists|k1: int, k2: int| 0 <= k1 < k2 < result.len() && 
            result[k1] as nat == lst[i] as nat && result[k2] as nat == lst[j] as nat,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}