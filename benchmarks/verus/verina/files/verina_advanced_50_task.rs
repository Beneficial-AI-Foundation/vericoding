// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(v: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> #[trigger] v[i] <= #[trigger] v[j]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn merge_sorted(a1: &Vec<u8>, a2: &Vec<u8>) -> (result: Vec<u8>)
    requires 
        is_sorted(a1@.map(|i: int, x: u8| x as nat)),
        is_sorted(a2@.map(|i: int, x: u8| x as nat)),
    ensures
        is_sorted(result@.map(|i: int, x: u8| x as nat)),
        result@.map(|i: int, x: u8| x as nat).to_multiset() == a1@.map(|i: int, x: u8| x as nat).to_multiset().add(a2@.map(|i: int, x: u8| x as nat).to_multiset()),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}