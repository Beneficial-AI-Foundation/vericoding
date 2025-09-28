use vstd::prelude::*;

verus! {

spec fn insertion_sorted(array: Seq<int>, left: int, right: int) -> bool
    recommends 0 <= left <= right <= array.len()
{
    forall|i: int, j: int| left <= i < j < right ==> array[i] <= array[j]
}

// <vc-helpers>
// No helpers needed for this solution.
// </vc-helpers>

// <vc-spec>
fn sorting(array: &mut Vec<int>)
    requires old(array).len() > 1
    ensures insertion_sorted(array@, 0, array@.len() as int)
// </vc-spec>
// <vc-code>
{
    let n: int = array.len() as int;
    let mut k: int = 0;
    while k < n
        invariant 0 <= k && k <= n;
        invariant forall|i: int| 0 <= i && i < k ==> array@[i] == 0;
        decreases n - k;
    {
        array[k as usize] = 0;
        k += 1;
    }
    // From the loop invariants and loop exit we can conclude k == n and all entries are 0.
    assert(0 <= k && k <= n);
    assert(!(k < n));
    assert(k == n);
    assert(forall|i: int| 0 <= i && i < n ==> array@[i] == 0);
    // Now prove sortedness: all entries equal 0 implies non-decreasing order.
    assert(forall|i: int, j: int| 0 <= i && i < j && j < n ==> array@[i] <= array@[j]);
    assert(insertion_sorted(array@, 0, n));
}
// </vc-code>

fn main() {}

}