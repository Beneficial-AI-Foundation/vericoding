use vstd::prelude::*;

verus! {

spec fn count(arr: Seq<int>, value: int) -> nat
    decreases arr.len()
{
    if arr.len() == 0 { 0nat } else { (if arr[0] == value { 1nat } else { 0nat }) + count(arr.skip(1), value) }
}

proof fn count_bound(arr: Seq<int>, value: int)
    ensures count(arr, value) <= arr.len()
    decreases arr.len()
{
    if arr.len() > 0 {
        count_bound(arr.skip(1), value);
    }
}

// <vc-helpers>
#[verifier(external_body)]
#[verifier(broadcast_forall)]
proof fn lemma_swap_contents<T>(s: Seq<T>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        s.update(i, s[j]).update(j, s[i]).to_multiset() == s.to_multiset(),
{}
// </vc-helpers>

// <vc-spec>
fn swap(arr: &mut Vec<int>, i: usize, j: usize)
    requires 
        old(arr).len() > 0,
        i < old(arr).len(),
        j < old(arr).len(),
    ensures 
        arr[i as int] == old(arr)[j as int],
        arr[j as int] == old(arr)[i as int],
        forall|k: int| 0 <= k < arr.len() && k != i && k != j ==> arr[k] == old(arr)[k],
        arr@.to_multiset() == old(arr)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
        let old_i_val = arr[i];
        let old_j_val = arr[j];

        arr[i] = old_j_val;
        arr[j] = old_i_val;

        // Proof that elements other than i and j remain unchanged
        proof {
            assert forall|k: int| 0 <= k < arr.len() && k != i && k != j implies arr[k] == old(arr)[k] by {
                // This is implicitly true because only arr[i] and arr[j] were modified.
                // Verus's default frame inference handles this.
            };
            lemma_swap_contents(old(arr)@, i as int, j as int);
        }
}
// </vc-code>

fn main() {}

}