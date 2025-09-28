use vstd::prelude::*;

verus! {

spec fn sorted(a: &[int]) -> bool {
    forall|j: int, k: int| 0 <= j < k < a.len() ==> a[j] <= a[k]
}

// <vc-helpers>
spec fn sorted_sub(a: &[int], low: int, high: int) -> bool {
    forall|j: int, k: int| low <= j < k < high ==> a[j] <= a[k]
}

proof fn lemma_sorted_sub(a: &[int], low: int, high: int)
    requires
        sorted(a),
        0 <= low <= high <= a.len(),
    ensures
        sorted_sub(a, low, high),
{
}

proof fn lemma_sorted_sub_transitive(a: &[int], low: int, mid: int, high: int)
    requires
        sorted_sub(a, low, mid),
        sorted_sub(a, mid, high),
    ensures
        sorted_sub(a, low, high),
{
}

spec fn contains(a: &[int], value: int, low: int, high: int) -> bool {
    exists|k: int| low <= k < high && a[k] == value
}

proof fn lemma_contains_contra(a: &[int], value: int, low: int, high: int)
    requires
        !contains(a, value, low, high),
    ensures
        forall|k: int| low <= k < high ==> a[k] != value,
{
}

proof fn lemma_array_index_property(a: &[int], idx: usize)
    ensures
        a[idx as int] == a[idx],
{
}
// </vc-helpers>

// <vc-spec>
fn binary_search(a: &[int], value: int) -> (index: i32)
    requires 
        sorted(a),
    ensures 
        0 <= index ==> index < a.len() && a[index as int] == value,
        index < 0 ==> forall|k: int| 0 <= k < a.len() ==> a[k] != value,
// </vc-spec>
// <vc-code>
{
    let mut low: usize = 0;
    let mut high: usize = a.len();
    let mut result: i32 = -1;
    
    while low < high
        invariant
            0 <= low <= high <= a.len(),
            sorted_sub(a, low as int, high as int),
            result == -1 ==> !contains(a, value, low as int, high as int),
            result >= 0 ==> (result as usize) < a.len() && a[result as usize] == value,
    {
        let mid = low + (high - low) / 2;
        assert(low <= mid);
        assert(mid < high);
        
        proof {
            lemma_array_index_property(a, mid);
        }
        
        if a[mid] == value {
            result = mid as i32;
            break;
        } else if a[mid] < value {
            proof {
                lemma_sorted_sub(a, low as int, high as int);
            }
            low = mid + 1;
            proof {
                assert forall|k: int| (low as int) <= k < (high as int) implies a[k] != value by {
                    if (mid as int) <= k < high as int {
                        assert(a[mid as int] <= a[k]);
                        assert(a[mid] < value);
                    }
                };
            }
        } else {
            proof {
                lemma_sorted_sub(a, low as int, high as int);
            }
            high = mid;
            proof {
                assert forall|k: int| (low as int) <= k < (high as int) implies a[k] != value by {
                    if low as int <= k < mid as int {
                        assert(a[k] <= a[mid as int]);
                        assert(a[mid] > value);
                    }
                };
            }
        }
    }
    
    if result >= 0 {
        result
    } else {
        proof {
            lemma_contains_contra(a, value, low as int, high as int);
        }
        -1
    }
}
// </vc-code>

fn main() {
}

}