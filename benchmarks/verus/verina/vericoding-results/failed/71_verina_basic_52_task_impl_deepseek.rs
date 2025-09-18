// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>


proof fn is_sorted_prefix(arr: Seq<int>, i: int) -> bool {
    forall|k: int, l: int| 0 <= k < l <= i ==> arr[k] <= arr[l]
}

proof fn swap_preserves_multiset(a: Seq<int>, i: int, j: int) 
    ensures
        a.update(i, a[j]).update(j, a[i]).to_multiset() =~= a.to_multiset()
{
    assert(a.update(i, a[j]).update(j, a[i])@.to_multiset() =~= a@.to_multiset());
}

proof fn swap_elements(a: Seq<int>, i: int, j: int) -> (result: Seq<int>)
    requires
        0 <= i < a.len(),
        0 <= j < a.len()
    ensures
        result.len() == a.len(),
        result[i] == a[j],
        result[j] == a[i],
        forall|k: int| 0 <= k < a.len() && k != i && k != j ==> result[k] == a[k],
        result.to_multiset() =~= a.to_multiset()
{
    let result = a.update(i, a[j]).update(j, a[i]);
    result
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
    /* code modified by LLM (iteration 5): Fixed implies syntax and improved loop invariants */
    let mut arr = a.clone();
    let n = arr.len();
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            arr@.to_multiset() == a@.to_multiset(),
            forall|k: int, l: int| 0 <= k < l < i ==> arr@[k] <= arr@[l]
        decreases n - i
    {
        let mut j: usize = 0;
        while j < n - i - 1
            invariant
                j <= n - i - 1,
                arr@.to_multiset() == a@.to_multiset(),
                forall|k: int, l: int| 0 <= k < l < i ==> arr@[k] <= arr@[l],
                forall|k: int| 0 <= k < j ==> arr@[k] <= arr@[k + 1]
            decreases n - i - 1 - j
        {
            if arr[j] > arr[j + 1] {
                proof {
                    swap_preserves_multiset(arr@, j as int, (j + 1) as int);
                }
                let temp = arr[j];
                arr[j] = arr[j + 1];
                arr[j + 1] = temp;
            }
            j += 1;
        }
        i += 1;
    }
    arr
}
// </vc-code>

}
fn main() {}