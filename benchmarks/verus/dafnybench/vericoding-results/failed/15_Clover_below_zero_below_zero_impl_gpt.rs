use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Vec<i32>) -> (result: (Vec<i32>, bool))
    ensures
        result.0.len() == operations.len() + 1,
        result.0[0] == 0,
        forall|i: int| 0 <= i < (result.0.len() - 1) as int ==> result.0[i + 1] == result.0[i] + operations[i],
        result.1 == true ==> exists|i: int| 1 <= i <= operations.len() as int && result.0[i] < 0,
        result.1 == false ==> forall|i: int| 0 <= i < result.0.len() as int ==> result.0[i] >= 0,
// </vc-spec>
// <vc-code>
{
    let mut res: Vec<i32> = Vec::new();
    res.push(0);
    let mut neg: bool = false;
    let mut i: usize = 0;

    while i < operations.len()
        invariant
            0 <= i <= operations.len(),
            res.len() == i + 1,
            res@[0] == 0,
            forall|j: int|
                0 <= j < i as int ==>
                    #[trigger] res@[j + 1] == res@[j] + operations@[j],
            neg ==> exists|k: int| 1 <= k <= i as int && #[trigger] res@[k] < 0,
            neg == false ==> forall|k: int| 0 <= k <= i as int ==> #[trigger] res@[k] >= 0,
        decreases operations.len() - i
    {
        let old_i = i;
        let ghost old_res = res@;
        let old_len = res.len();
        assert(old_len == old_i + 1);

        let prev = res[old_len - 1];
        assert(old_res.len() == old_len as int);
        assert(prev == old_res[old_len as int - 1]);
        assert(prev == old_res[old_i as int]);

        let op = operations[i];
        let next = prev + op;

        res.push(next);
        assert(res.len() == old_len + 1);
        // After push, previous elements are unchanged and last element is next
        assert(res@[old_i as int] == old_res[old_i as int]);
        assert(old_i + 1 == old_len);
        assert(res@[res.len() as int - 1] == next);
        assert(res@[old_i as int + 1] == next);

        // Establish the recurrence for j == old_i at the new i
        assert(res@[old_i as int + 1] == res@[old_i as int] + operations@[old_i as int]);

        if next < 0 {
            neg = true;
            // Provide a witness for negativity at k = old_i + 1
            proof {
                assert(1 <= old_i as int + 1);
                assert(old_i as int + 1 <= (old_i + 1) as int);
                assert(res@[old_i as int + 1] < 0);
            }
        } else {
            // neg remains as before; maintain invariants
            if neg {
                // Keep the previous witness
                proof {
                    assert(exists|k: int| 1 <= k <= old_i as int && old_res[k] < 0);
                    // Elements up to old_i are unchanged after push
                    assert(forall|k: int| 0 <= k <= old_i as int ==> #[trigger] res@[k] == old_res[k]);
                }
            } else {
                // Need to show nonnegativity up to i_new = old_i + 1
                proof {
                    // For k <= old_i, it follows from the previous invariant
                    // For k = old_i + 1, it follows from next >= 0
                    assert(res@[old_i as int + 1] >= 0);
                }
            }
        }

        i = i + 1;
    }

    (res, neg)
}
// </vc-code>

fn main() {}

}