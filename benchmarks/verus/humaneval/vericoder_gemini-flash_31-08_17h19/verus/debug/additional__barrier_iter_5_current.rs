use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::loop_isolation(false)]
proof fn lemma_p_barrier_k_le_p_l_gt_p_implies_arr_k_lt_arr_l(
    arr: &[i32],
    p: usize,
    k_prime: int,
    k_prime_idx_valid: bool,
    l_idx: int,
    l_idx_valid: bool,
)
    requires
        arr.len() > 0,
        0 <= p < arr.len(),
        forall|k: int, l: int| 0 <= k <= p && p < l < arr.len() ==> arr[k] < arr[l],
        k_prime_idx_valid == (0 <= k_prime && k_prime <= p as int),
        l_idx_valid == (p as int < l_idx && l_idx < arr.len() as int),
    ensures
        k_prime_idx_valid && l_idx_valid ==> arr[k_prime as usize] < arr[l_idx as usize],
{
    if k_prime_idx_valid && l_idx_valid {
        assert(arr[k_prime as usize] < arr[l_idx as usize]);
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn barrier(arr: &[i32], p: usize) -> (result: bool)
    // pre-conditions-start
    requires
        arr.len() > 0,
        0 <= p < arr.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == forall|k: int, l: int| 0 <= k <= p && p < l < arr.len() ==> arr[k] < arr[l],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut result: bool = true;

    while (i <= p) && result
        invariant
            arr.len() > 0,
            0 <= p < arr.len(),
            0 <= i <= p + 1,
            result == (forall|k: int| 0 <= k < i as int ==> (forall|l: int| p as int < l && l < arr.len() as int ==> arr[k as usize] < arr[l as usize])),
    {
        let mut j: usize = p + 1;
        while (j < arr.len()) && result
            invariant
                arr.len() > 0,
                0 <= p < arr.len(),
                0 <= i <= p,
                p < j <= arr.len(),
                result == (forall|k: int| 0 <= k < i as int ==> (forall|l: int| p as int < l && l < arr.len() as int ==> arr[k as usize] < arr[l as usize]))
                    && (forall|l: int| (p + 1) as int <= l && l < j as int ==> arr[i as usize] < arr[l as usize]),
        {
            if arr[i as usize] >= arr[j as usize] {
                result = false;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}
}