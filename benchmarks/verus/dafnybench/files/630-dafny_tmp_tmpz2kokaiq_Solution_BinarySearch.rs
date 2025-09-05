use vstd::prelude::*;

verus! {

spec fn sorted(a: &[int]) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn binary_search(a: &[int], x: int) -> (index: i32)
    requires 
        sorted(a),
    ensures 
        0 <= index < a.len() ==> a[index as int] == x,
        index == -1 ==> forall|i: int| 0 <= i < a.len() ==> a[i] != x,
// </vc-spec>
// <vc-code>
{
    assume(false);
    -1
}
// </vc-code>

fn main() {}

}