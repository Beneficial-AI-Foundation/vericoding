use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_sorted_distinct_missing(arr: Seq<i32>, v: i32) 
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
        forall|i: int| 0 <= i < arr.len() ==> arr[i] >= 0,
        0 <= v,
        forall|i: int| 0 <= i < arr.len() ==> arr[i] != v,
        forall|k: int| 0 <= k < v ==> exists|j: int| 0 <= j < arr.len() && arr[j] == k,
    ensures
        v == arr.len() as i32 || v < arr.len() as i32 && arr[v as usize] != v
{
}

proof fn lemma_inductive_step(arr: Seq<i32>, k: int)
    requires
        0 <= k < arr.len() as int,
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
        forall|i: int| 0 <= i < arr.len() ==> arr[i] >= 0,
        forall|i: int| 0 <= i < k ==> exists|j: int| 0 <= j < arr.len() && arr[j] == i,
        arr[k as usize] != k,
    ensures
        forall|i: int| 0 <= i <= k ==> exists|j: int| 0 <= j < arr.len() && arr[j] != i
{
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn smallest_missing_number(s: &[i32]) -> (v: i32)
    // pre-conditions-start
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        s.len() <= 100_000,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= v,
        forall|i: int| 0 <= i < s.len() ==> s[i] != v,
        forall|k: int| 0 <= k < v && s[k] != v ==> exists|j: int| 0 <= j < s.len() && s[j] == k,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = s.len();
    let mut low: usize = 0;
    let mut high: usize = n;
    
    while low < high
        invariant
            0 <= low <= high <= n,
            forall|i: int| 0 <= i < low ==> exists|j: int| 0 <= j < n && s[j] == i,
            forall|i: int| low <= i < high ==> i < n as int ==> s[i] != i,
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        assert(0 <= mid < n || mid == n);
        
        if mid < n && s[mid] == mid as i32 {
            proof {
                assert(s[mid] == mid as i32);
            }
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    
    let result = low as i32;
    
    proof {
        assert(0 <= result);
        assert(forall|i: int| 0 <= i < n ==> s[i] != result);
        
        assert forall|k: int| 0 <= k < result implies exists|j: int| 0 <= j < n && s[j] == k by {
            assert(k < low as int);
        };
    }
    
    result
}
// </vc-code>

fn main() {}
}