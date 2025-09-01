use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_sorted_property(s: &[i32], i: int, j: int)
    requires
        forall|x: int, y: int| 0 <= x < y < s.len() ==> s[x] <= s[y],
        0 <= i <= j < s.len(),
    ensures
        s[i] <= s[j]
{
    if i < j {
        assert(s[i] <= s[j]);
    } else {
        assert(i == j);
        assert(s[i] == s[j]);
    }
}

proof fn lemma_binary_search_bounds(s: &[i32], target: i32, left: int, right: int, mid: int)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        0 <= left <= right < s.len(),
        mid == (left + right) / 2,
        left <= mid < right,
    ensures
        left <= mid <= right,
        0 <= mid < s.len(),
{
}

proof fn lemma_found_all_smaller(s: &[i32], target: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        forall|k: int| 0 <= k < target ==> exists|j: int| 0 <= j < s.len() && #[trigger] s[j] == k,
        forall|i: int| 0 <= i < s.len() ==> s[i] != target,
    ensures
        true,
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
    let mut candidate = 0i32;
    
    while candidate < s.len() as i32
        invariant
            0 <= candidate <= s.len(),
            forall|k: int| 0 <= k < candidate ==> exists|j: int| 0 <= j < s.len() && #[trigger] s[j] == k,
            forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
            forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        decreases s.len() - candidate
    {
        let mut found = false;
        let mut i = 0;
        
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                found <==> exists|j: int| 0 <= j < i && #[trigger] s[j] == candidate,
                forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
                forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
                0 <= candidate <= s.len(),
            decreases s.len() - i
        {
            if s[i] == candidate {
                found = true;
                break;
            }
            i += 1;
        }
        
        if !found {
            assert(forall|j: int| 0 <= j < s.len() ==> s[j] != candidate);
            return candidate;
        }
        
        candidate += 1;
    }
    
    assert(forall|k: int| 0 <= k < candidate ==> exists|j: int| 0 <= j < s.len() && #[trigger] s[j] == k);
    assert(candidate == s.len());
    assert(forall|j: int| 0 <= j < s.len() ==> s[j] != candidate);
    
    candidate
}
// </vc-code>

fn main() {}
}