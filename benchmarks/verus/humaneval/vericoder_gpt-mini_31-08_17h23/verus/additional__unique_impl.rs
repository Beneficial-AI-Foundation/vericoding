use vstd::prelude::*;

verus! {

// <vc-helpers>
// Added no helpers; kept empty as proofs are done inline in the code.
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn unique(a: &[i32]) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let n: int = a.len() as int;
    if n == 0 {
        return vec![];
    }

    let mut res: Vec<i32> = vec![a[0]];
    let mut i: int = 1;

    while i < n
        invariant 1 <= i && i <= n
        invariant (res.len() as int) >= 1
        invariant forall |u: int, v: int| #[trigger res@[u], res@[v]] 0 <= u && u < v && v < (res.len() as int) ==> res@[u] < res@[v]
        invariant forall |j: int| #[trigger res] 0 <= j && j < i ==> exists |t: int| 0 <= t && t < (res.len() as int) && res@[t] == a[j]
        invariant forall |t: int| #[trigger res@[t]] 0 <= t && t < (res.len() as int) ==> exists |p: int| 0 <= p && p < i && res@[t] == a[p]
        decreases n - i
    {
        let old_len: int = res.len() as int;
        // capture the current last element (exists because res.len() >= 1)
        let last: i32 = res@[(old_len) - 1];

        if a[i] != last {
            // We will push a[i], so after push the new last element equals a[i].
            // Prove preservation of invariants after the push.
            //
            // Save witnesses from the old invariants
            assert(old_len >= 1);

            // From the invariant mapping res elements to some a[p] with p < i,
            // get a witness for the old last element.
            assert(exists |p: int| 0 <= p && p < i && res@[(old_len) - 1] == a[p]);
            let p = choose(|p: int| 0 <= p && p < i && res@[(old_len) - 1] == a[p]);

            // By the input non-decreasing precondition, a[p] <= a[i]
            assert(a[p] <= a[i]);

            // Since a[i] != res.last and res.last == a[p], we have res.last < a[i]
            assert(res@[(old_len) - 1] < a[i]);

            // Now perform the push
            res.push(a[i]);

            // After push, new_len = old_len + 1
            let new_len: int = res.len() as int;
            assert(new_len == old_len + 1);

            // Re-establish mapping invariant for the newly pushed element:
            // res@[new_len-1] == a[i] and witness p' = i satisfies 0 <= p' < i+1
            // (this will be used when i is incremented)
            assert(res@[new_len - 1] == a[i]);

            // Re-establish strict monotonicity:
            // For any u < v < new_len:
            // - if v < old_len then old invariant gives res@[u] < res@[v]
            // - if v == new_len-1 then for any u < old_len: res@[u] < res@[old_len-1] < a[i] = res@[new_len-1]
            //
            // We encode these facts as assertions to help the verifier.
            // For arbitrary index u with 0 <= u && u < old_len - 1, res@[u] < res@[old_len-1]
            // follows from the old strictness invariant.
            assert(forall |u: int| #[trigger res@[u], res@[(old_len) - 1]] 0 <= u && u < (old_len - 1) ==> res@[u] < res@[(old_len) - 1]);
            // Combine with res@[(old_len)-1] < a[i] to get res@[u] < a[i] for u < old_len
            assert(forall |u: int| #[trigger res@[u], res@[new_len - 1]] 0 <= u && u < old_len ==> res@[u] < res@[new_len - 1]);

            // Now the overall strictness for all pairs in [0, new_len) holds:
            // - pairs both < old_len: old invariant
            // - pairs with v == new_len-1: just shown
            // We assert the combined universal fact to satisfy the loop invariant.
            assert(forall |u: int, v: int| #[trigger res@[u], res@[v]] 0 <= u && u < v && v < new_len ==> res@[u] < res@[v]);
        } else {
            // a[i] == last, so nothing changes in res; existing invariants still hold.
            assert(res@[(old_len) - 1] == a[i]);
        }

        // Re-establish the mapping invariant for all j < i+1:
        // For j < i it holds by the loop invariant. For j == i, either
        // - we did not push and last == a[i] gives a witness t = old_len - 1, or
        // - we pushed and the new last index (res.len()-1) holds a[i] with witness t = res.len()-1.
        assert(forall |j: int| #[trigger res] 0 <= j && j < i + 1 ==>
            exists |t: int| 0 <= t && t < (res.len() as int) && res@[t] == a[j]);

        // Increment loop counter
        i += 1;
    }

    // After loop, i == n, invariants give that res is strictly increasing.
    res
    // impl-end
}
// </vc-code>

fn main() {}
}