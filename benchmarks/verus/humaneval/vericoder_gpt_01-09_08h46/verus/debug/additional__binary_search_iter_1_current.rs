use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_half_less_than_n(n: int)
    requires
        0 < n,
    ensures
        0 <= n / 2 && n / 2 < n,
{
    assert(0 <= n / 2);
    // If n > 0, then floor(n/2) < n
    if n == 1 {
        assert(n / 2 == 0);
        assert(0 < n);
    } else {
        // n >= 2
        assert(n >= 2);
        // For integers, if n >= 2 then n/2 <= n-1, hence n/2 < n
        assert(n / 2 <= n - 1);
        assert(n - 1 < n);
        assert(n / 2 < n);
    }
}

proof fn lemma_prefix_excludes_target_if_mid_less(arr: &[i32], target: i32, k: int)
    requires
        0 <= k && k < arr.len(),
        arr[k] < target,
        forall|i: int, j: int| 0 <= i && i < j && j < arr.len() ==> arr[i] <= arr[j],
    ensures
        forall|i: int| 0 <= i && i <= k ==> arr[i] != target,
{
    assert_forall_by(|i: int| 0 <= i && i <= k ==> arr[i] != target, {
        requires(|i: int| 0 <= i && i <= k);
        ensures(|i: int| arr[i] != target);
        if i < k {
            assert(0 <= i && i < k);
            assert(k < arr.len());
            assert(arr[i] <= arr[k]);
            assert(arr[i] < target);
            assert(arr[i] != target);
        } else {
            assert(i == k);
            assert(arr[i] == arr[k]);
            assert(arr[i] != target);
        }
    });
}

proof fn lemma_suffix_excludes_target_if_mid_greater(arr: &[i32], target: i32, k: int)
    requires
        0 <= k && k < arr.len(),
        arr[k] > target,
        forall|i: int, j: int| 0 <= i && i < j && j < arr.len() ==> arr[i] <= arr[j],
    ensures
        forall|j: int| k <= j && j < arr.len() ==> arr[j] != target,
{
    assert_forall_by(|j: int| k <= j && j < arr.len() ==> arr[j] != target, {
        requires(|j: int| k <= j && j < arr.len());
        ensures(|j: int| arr[j] != target);
        if k < j {
            assert(0 <= k && k < j && j < arr.len());
            assert(arr[k] <= arr[j]);
            assert(arr[j] >= arr[k]);
            assert(arr[j] > target);
            assert(arr[j] != target);
        } else {
            assert(j == k);
            assert(arr[j] == arr[k]);
            assert(arr[j] != target);
        }
    });
}

proof fn lemma_combine_not_found(arr: &[i32], lo: int, hi: int, target: i32)
    requires
        0 <= lo && lo == hi && hi <= arr.len(),
        forall|i: int| 0 <= i && i < lo ==> arr[i] != target,
        forall|i: int| hi <= i && i < arr.len() ==> arr[i] != target,
    ensures
        forall|i: int| 0 <= i && i < arr.len() ==> arr[i] != target,
{
    assert_forall_by(|i: int| 0 <= i && i < arr.len() ==> arr[i] != target, {
        requires(|i: int| 0 <= i && i < arr.len()));
        ensures(|i: int| arr[i] != target);
        if i < lo {
            assert(arr[i] != target);
        } else {
            assert(lo <= i);
            assert(hi <= i); // since lo == hi
            assert(arr[i] != target);
        }
    });
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn binary_search(arr: &[i32], target: i32) -> (result: Option<usize>)
    // pre-conditions-start
    requires
        forall|i: int, j: int| 0 <= i && i < j && j < arr.len() ==> arr[i] <= arr[j],
    // pre-conditions-end
    // post-conditions-start
    ensures
        match result {
            Some(index) => arr[index as int] == target && arr.len() > 0 && index < arr.len(),
            None => forall|i: int| 0 <= i && i < arr.len() ==> arr[i] != target,
        },
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut lo: usize = 0;
    let mut hi: usize = arr.len();

    while lo < hi
        invariant
            0 <= (lo as int) && (lo as int) <= (hi as int) && (hi as int) <= arr.len(),
            forall|i: int| 0 <= i && i < (lo as int) ==> arr[i] != target,
            forall|i: int| (hi as int) <= i && i < arr.len() ==> arr[i] != target,
            forall|i: int, j: int| 0 <= i && i < j && j < arr.len() ==> arr[i] <= arr[j],
        decreases (hi as int) - (lo as int)
    {
        let mid: usize = lo + (hi - lo) / 2;

        // Prove lo <= mid < hi
        proof {
            let n: int = (hi as int) - (lo as int);
            assert(0 < n);
            lemma_half_less_than_n(n);
            assert((lo as int) + n / 2 < (lo as int) + n);
            assert((mid as int) == (lo as int) + n / 2);
            assert((mid as int) < (hi as int));
            assert((lo as int) <= (mid as int));
        }
        assert(mid < hi);
        assert(lo <= mid);
        assert((mid as int) < arr.len());

        let v = arr[mid];
        if v == target {
            proof {
                // From loop condition lo < hi, we know arr has length > 0
                assert((hi as int) <= arr.len());
                assert((lo as int) < (hi as int));
                assert(0 < arr.len());
            }
            return Some(mid);
        } else if v < target {
            // Update left bound: exclude up to and including mid
            proof {
                lemma_prefix_excludes_target
// </vc-code>

fn main() {}
}