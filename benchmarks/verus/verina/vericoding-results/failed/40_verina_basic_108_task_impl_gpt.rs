// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn helper_trivial() { }
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: &Vec<i32>) -> (result: (Vec<i32>, bool))
    ensures
        result.0.len() == operations.len() + 1,
        result.0[0] == 0,
        forall|i: int| 0 <= i < operations.len() ==> result.0[i + 1] == result.0[i] + operations[i],
        result.1 == (exists|i: int| 1 <= i < result.0.len() && result.0[i] < 0),
// </vc-spec>
// <vc-code>
{
    let mut res: Vec<i32> = Vec::new();
    res.push(0);
    let mut i: usize = 0;

    while i < operations.len()
        invariant
            0 <= i as int <= operations.len(),
            res.len() == i as int + 1,
            res[0] == 0,
            forall|j: int| 0 <= j < res.len() - 1 ==> res[j + 1] == res[j] + operations[j],
        decreases operations.len() - i
    {
        let prev_len = res.len();
        let prev = res[prev_len - 1];
        let next = prev + operations[i];
        res.push(next);
        i = i + 1;

        proof {
            let old_len = prev_len as int;
            assert forall|j: int| 0 <= j < res.len() - 1 ==> res[j + 1] == res[j] + operations[j]
            by {
                if j < old_len - 1 {
                    // For j in the old range, the property was preserved by push
                } else {
                    assert(j == old_len - 1);
                    assert(res[old_len] == next);
                    assert(res[old_len - 1] == prev);
                    assert(res[j + 1] == res[j] + operations[j]);
                }
            };
        }
    }

    let mut found: bool = false;
    let mut j: usize = 1;
    while j < res.len()
        invariant
            1 <= j as int <= res.len(),
            found == (exists|k: int| 1 <= k < j as int && res[k] < 0),
        decreases res.len() - j
    {
        if res[j] < 0 {
            found = true;
        }
        j = j + 1;
    }

    (res, found)
}
// </vc-code>

}
fn main() {}