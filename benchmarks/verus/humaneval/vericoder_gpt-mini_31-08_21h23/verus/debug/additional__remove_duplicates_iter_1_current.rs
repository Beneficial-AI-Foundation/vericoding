use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
// No helpers required for this proof.
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        a.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int| #![auto] 0 <= i < result.len() ==> in_array(a@, result[i]),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut result: Vec<i32> = Vec::new();
    let n: int = a.len() as int;
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n;
        invariant forall|t: int| 0 <= t < (result.len() as int) ==> in_array(a@, result[t]);
        invariant forall|p: int, q: int| 0 <= p < q < (result.len() as int) ==> result[p] != result[q];
    {
        let cur: i32 = a[i as usize];

        // inner loop: check if cur is already in result
        let mut k: int = 0;
        let mut found: bool = false;
        while k < (result.len() as int)
            invariant 0 <= k && k <= (result.len() as int);
            invariant found == (exists|j: int| 0 <= j < k && #[trigger] result@[j] == cur);
            invariant forall|p: int, q: int| 0 <= p < q < (result.len() as int) ==> result[p] != result[q];
            invariant forall|t: int| 0 <= t < (result.len() as int) ==> in_array(a@, result[t]);
        {
            if result[k as usize] == cur {
                found = true;
            }
            k += 1;
        }

        if !found {
            let old_len: int = result.len() as int;
            // from the inner loop invariant with k == old_len we have: found == exists j < old_len . result@[j] == cur
            // so !found implies no such j exists.
            proof {
                assert(!(exists|j: int| 0 <= j < old_len && result@[j] == cur));
                // cur equals a@[i], hence cur is in a@ at index i
                assert(a@[i] == cur);
                assert(in_array(a@, cur));
            }
            result.push(cur);
            proof {
                // After push, result.len() == old_len + 1
                // show element at old_len is cur
                assert(result@[old_len] == cur);
                // show all elements are from a@
                assert(forall|t: int| 0 <= t < old_len ==> in_array(a@, result[t]));
                assert(in_array(a@, result@[old_len]));
                // show uniqueness:
                //  - previous pairs with q < old_len keep being distinct
                assert(forall|p: int, q: int| 0 <= p < q < old_len ==> result[p] != result[q]);
                //  - new pairs with q == old_len: result[p] != result[old_len] because no j < old_len had value cur
                assert(forall|p: int| 0 <= p < old_len ==> result[p] != result@[old_len]);
                // combine to the full uniqueness for length old_len+1
                assert(forall|p: int, q: int| 0 <= p < q < (old_len + 1) ==> result[p] != result[q]);
            }
        }

        i += 1;
    }

    // return
    result
    // impl-end
}
// </vc-code>

fn main() {}
}