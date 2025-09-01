use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_sorted_bounds(s: Seq<i32>, i: int, j: int)
    requires
        forall|k: int, l: int| 0 <= k && k < l && l < s.len() ==> s[k] <= s[l],
        0 <= i <= j < s.len()
    ensures
        s[i] <= s[j]
{
}

proof fn lemma_elem_in_sorted_seq(s: Seq<i32>, target: i32, low: int, high: int) 
    requires
        forall|i: int, j: int| 0 <= i && i < j && j < s.len() ==> s[i] <= s[j],
        0 <= low <= high < s.len(),
        s[low] <= target <= s[high]
    ensures
        exists|i: int| low <= i <= high && s[i] == target
    decreases high - low
{
    if low == high {
        assert(s[low] <= target <= s[low] ==> s[low] == target);
    } else {
        let mid = (low + high) / 2;
        lemma_seq_sorted_bounds(s, low, high);
        lemma_seq_sorted_bounds(s, low, mid);
        lemma_seq_sorted_bounds(s, mid, high);
        
        if s[mid] == target {
        } else if s[mid] < target {
            lemma_elem_in_sorted_seq(s, target, mid + 1, high);
        } else {
            lemma_elem_in_sorted_seq(s, target, low, mid - 1);
        }
    }
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
    let mut low: usize = 0;
    let mut high: usize = arr.len();
    if high == 0 {
        proof {
            assert forall|i: int| 0 <= i && i < arr.len() implies arr[i] != target by {
                assert(arr.len() == 0);
            };
        }
        return None;
    }
    let mut high = high - 1;
    
    while low <= high
        invariant
            0 <= low <= high < arr.len() || (low == high + 1 && high < arr.len()),
            forall|i: int| 0 <= i && i < arr.len() && arr[i] == target ==> low <= i <= high,
        decreases high - low
    {
        let mid = (low + high) / 2;
        
        if arr[mid] == target {
            proof {
                assert(arr@[mid as int] == target);
            }
            return Some(mid);
        } else if arr[mid] < target {
            proof {
                let s = arr@;
                assert forall|i: int| 0 <= i && i < s.len() && s[i] == target implies (mid + 1) as int <= i <= high as int by {
                    lemma_seq_sorted_bounds(s, mid as int, i);
                    assert(s[i] == target);
                    assert(s[mid as int] < target);
                    assert(i > mid as int);
                };
            }
            low = mid + 1;
        } else {
            proof {
                let s = arr@;
                assert forall|i: int| 0 <= i && i < s.len() && s[i] == target implies low as int <= i <= (mid - 1) as int by {
                    lemma_seq_sorted_bounds(s, i, mid as int);
                    assert(s[i] == target);
                    assert(s[mid as int] > target);
                    assert(i < mid as int);
                };
            }
            if mid == 0 {
                break;
            }
            high = mid - 1;
        }
    }
    
    proof {
        let s = arr@;
        assert forall|i: int| 0 <= i && i < s.len() implies s[i] != target by {
            if s[i] == target {
                assert(low as int <= i <= high as int);
                assert(false);
            }
        };
    }
    None
}
// </vc-code>

fn main() {}
}