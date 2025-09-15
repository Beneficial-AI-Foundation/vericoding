// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed syntax errors and implemented proper helper functions */

spec fn sorted(a: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

spec fn multiset_equals(a: Seq<i32>, b: Seq<i32>) -> bool {
    a.to_multiset() =~= b.to_multiset()
}

proof fn lemma_insert_preserves_multiset(a: Seq<i32>, i: usize, v: i32)
    ensures
        a.insert(i, v)@.to_multiset() =~= a@.insert(v),
{
}

proof fn lemma_remove_preserves_multiset(a: Seq<i32>, i: usize)
    requires
        0 <= i < a.len(),
    ensures
        a.remove(i)@.to_multiset() =~= a@.remove(a[i]),
{
}

proof fn lemma_multiset_transitive(a: Seq<i32>, b: Seq<i32>, c: Seq<i32>)
    requires
        multiset_equals(a, b),
        multiset_equals(b, c),
    ensures
        multiset_equals(a, c),
{
}
// </vc-helpers>

// <vc-spec>
fn insertion_sort(l: Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],

        result@.to_multiset() == l@.to_multiset(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Simplified insertion sort implementation with proper verification */
{
    let mut arr = l;
    let mut i: usize = 1;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            sorted(arr@.subrange(0, i)),
            multiset_equals(arr@, l@),
    {
        let key = arr[i];
        let mut j = i;
        
        while j > 0 && arr[j - 1] > key
            invariant
                0 <= j <= i,
                (forall|k: int| j <= k < i ==> arr[k] > key),
                sorted(arr@.subrange(0, j)),
                sorted(arr@.subrange(j, i)),
                multiset_equals(arr@, l@),
        {
            arr.swap(j, j - 1);
            j -= 1;
        }
        
        i += 1;
    }
    
    arr
}
// </vc-code>

}
fn main() {}