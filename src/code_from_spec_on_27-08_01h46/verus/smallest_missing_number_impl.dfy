use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn contains_value(s: &[i32], val: i32) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == val
}

proof fn lemma_binary_search_bounds(s: &[i32], target: i32, left: usize, right: usize) -> (found: bool)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        left <= right,
        right <= s.len(),
    ensures
        found <==> exists|i: int| left <= i < right && s[i] == target,
    decreases right - left,
{
    if left >= right {
        false
    } else {
        let mid = left + (right - left) / 2;
        if s[mid] == target {
            true
        } else if s[mid] < target {
            lemma_binary_search_bounds(s, target, (mid + 1) as usize, right)
        } else {
            lemma_binary_search_bounds(s, target, left, mid as usize)
        }
    }
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
    let mut candidate = 0i32;
    
    while candidate < s.len() as i32
        invariant
            0 <= candidate,
            candidate <= s.len(),
            forall|k: int| 0 <= k < candidate ==> #[trigger] exists|j: int| 0 <= j < s.len() && s[j] == k,
        decreases s.len() - candidate,
    {
        // Binary search for candidate in s
        let mut left = 0usize;
        let mut right = s.len();
        let mut found = false;
        
        while left < right
            invariant
                left <= right,
                right <= s.len(),
                found <==> exists|i: int| 0 <= i < left && s[i] == candidate,
                !found ==> forall|i: int| 0 <= i < left ==> s[i] != candidate,
                forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
            decreases right - left,
        {
            let mid = left + (right - left) / 2;
            
            if s[mid] == candidate {
                found = true;
                break;
            } else if s[mid] < candidate {
                left = mid + 1;
            } else {
                right = mid;
            }
        }
        
        if !found {
            return candidate;
        }
        
        candidate += 1;
    }
    
    candidate
}
// </vc-code>

fn main() {}
}