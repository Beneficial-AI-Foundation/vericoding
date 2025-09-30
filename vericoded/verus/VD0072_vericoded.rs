use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
// </vc-helpers>

// <vc-spec>
fn min_array(a: &[i32]) -> (r: i32)
    requires a.len() > 0,
    ensures forall|i: int| 0 <= i < a.len() ==> r <= a[i],
    // Note: Verus currently has syntax limitations with exists quantifiers in postconditions
    // The second ensures clause from Dafny cannot be directly translated
// </vc-spec>
// <vc-code>
{
    let mut min_val: i32 = a[0];
    let mut j: usize = 1usize;

    proof {
        // min_val == a@[0], so the invariant holds for j = 1
        assert(min_val == a@[0]);
        assert(forall|k: int| 0 <= k && k < 1 as int ==> min_val <= a@[k]);
    }

    while j < a.len()
        invariant
            j <= a.len(),
            forall|k: int| 0 <= k && k < j as int ==> min_val <= a@[k]
        decreases a.len() - j
    {
        let old = min_val;
        let ai: i32 = a[j];

        // old == min_val and the loop invariant gives forall k < j ==> old <= a@[k]
        proof {
            assert(old == min_val);
            assert(forall|k: int| 0 <= k && k < j as int ==> old <= a@[k]);
        }

        if ai < old {
            min_val = ai;
            proof {
                // min_val == ai
                assert(min_val == ai);
                // For k < j: ai <= old and old <= a@[k] (from invariant) implies ai <= a@[k]
                assert(ai <= old);
                assert(forall|k: int| 0 <= k && k < j as int ==> min_val <= a@[k]);
            }
        } else {
            // min_val remains old; the previous invariant still holds
            proof {
                assert(min_val == old);
                assert(forall|k: int| 0 <= k && k < j as int ==> min_val <= a@[k]);
            }
        }

        // prove min_val <= a@[j] for the current j (so it holds for k = j when j is incremented)
        proof {
            if ai < old {
                assert(min_val == ai);
                assert(ai == a@[j as int]);
                assert(min_val <= a@[j as int]);
            } else {
                // !(ai < old) implies ai >= old, so old <= ai
                assert(old <= ai);
                assert(old == min_val);
                assert(ai == a@[j as int]);
                assert(min_val <= a@[j as int]);
            }
        }

        j = j + 1usize;
    }

    min_val
}
// </vc-code>

fn main() {}

}