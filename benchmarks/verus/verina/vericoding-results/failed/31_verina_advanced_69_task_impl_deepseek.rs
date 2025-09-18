// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed while loops from proof helper, restructured with assertions */
pub proof fn binary_search_lemma(xs: Seq<i32>, target: i32, low: int, high: int, mid: int) 
    requires 
        low >= 0 && high <= xs.len() && low <= high,
        forall|i: int, j: int| 0 <= i < j < xs.len() ==> xs[i] < xs[j],
        mid == (low + high) / 2,
    ensures 
        (target <= xs[mid] ==> (forall|j: int| mid <= j < high ==> target <= xs[j]) && (forall|j: int| 0 <= j < mid ==> xs[j] < target)) &&
        (xs[mid] < target ==> (forall|j: int| low <= j <= mid ==> xs[j] < target) && (forall|j: int| mid < j < xs.len() ==> target <= xs[j]))
{
    if target <= xs[mid] {
        assert forall|j: int| mid <= j < high implies target <= xs[j] by {
            assert forall|j: int| mid <= j < high ensures target <= xs[j] {
                assert(mid >= 0 && j < xs.len());
                assert(xs[mid] <= xs[j]);
                assert(target <= xs[mid]);
            }
        };
        assert forall|j: int| 0 <= j < mid implies xs[j] < target by {
            assert forall|j: int| 0 <= j < mid ensures xs[j] < target {
                assert(j >= 0 && mid < xs.len());
                assert(xs[j] < xs[mid]);
                assert(xs[mid] >= target);
            }
        };
    } else {
        assert forall|j: int| low <= j <= mid implies xs[j] < target by {
            assert forall|j: int| low <= j <= mid ensures xs[j] < target {
                assert(j >= 0 && j < xs.len());
                assert(xs[j] <= xs[mid]);
                assert(xs[mid] < target);
            }
        };
        assert forall|j: int| mid < j < xs.len() implies target <= xs[j] by {
            assert forall|j: int| mid < j < xs.len() ensures target <= xs[j] {
                assert(j >= 0 && j < xs.len());
                assert(xs[mid] < xs[j]);
                assert(xs[mid] < target);
            }
        };
    }
}
// </vc-helpers>

// <vc-spec>
fn search_insert(xs: &Vec<i32>, target: i32) -> (result: usize)
    requires forall|i: int, j: int| 0 <= i < j < xs.len() ==> xs[i] < xs[j],
    ensures
        result <= xs.len(),
        forall|i: int| 0 <= i < result ==> xs[i] < target,
        result < xs.len() ==> target <= xs[result as int],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Removed proof block call since lemma is now property-based */
{
    let mut low: usize = 0;
    let mut high: usize = xs.len();
    
    while low < high
        invariant
            low <= high <= xs.len(),
            forall|i: int| 0 <= i < low as int ==> xs[i] < target,
            forall|i: int| high as int <= i < xs.len() as int ==> target <= xs[i]
        decreases high - low
    {
        let mid = (low + high) / 2;
        
        if xs[mid] < target {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    
    low
}
// </vc-code>

}
fn main() {}