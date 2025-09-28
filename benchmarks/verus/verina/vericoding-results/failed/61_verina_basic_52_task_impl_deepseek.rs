// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn bubble_sort_invariant(a: Seq<i32>, i: int, arr: Seq<i32>) -> bool {
    ensures ret ==> (
        arr.len() == a.len()
        && arr@.to_multiset() == a@.to_multiset()
        && (forall|k: int| 0 <= k < i ==> arr[k] <= arr[k + 1])
        && (forall|k: int| i <= k < arr.len() - 1 ==> arr[k] == a[k])
    );
    arr.len() == a.len()
    && arr@.to_multiset() == a@.to_multiset()
    && (forall|k: int| 0 <= k < i ==> arr[k] <= arr[k + 1])
    && (forall|k: int| i <= k < arr.len() - 1 ==> arr[k] == a[k])
}
// </vc-helpers>

// <vc-spec>
fn bubble_sort(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        a@.to_multiset() == result@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed syntax error by removing misplaced ensures clause */
    let mut result = a.clone();
    let n = result.len();
    
    proof {
        assert(bubble_sort_invariant(a@, 0, result@));
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            bubble_sort_invariant(a@, i as int, result@),
        decreases n - i,
    {
        let mut j: usize = 0;
        while j < n - i - 1
            invariant
                j <= n - i - 1,
                bubble_sort_invariant(a@, i as int, result@),
            decreases n - i - j - 1,
        {
            if result[j] > result[j + 1] {
                let temp = result[j];
                result[j] = result[j + 1];
                result[j + 1] = temp;
            }
            j += 1;
            
            proof {
                assert(bubble_sort_invariant(a@, i as int, result@));
            }
        }
        i += 1;
        
        proof {
            assert(bubble_sort_invariant(a@, i as int, result@));
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}