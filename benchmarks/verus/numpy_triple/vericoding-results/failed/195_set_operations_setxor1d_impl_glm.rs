// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn contains_element(arr: Seq<i32>, elem: i32) -> bool {
    exists|i: int| 0 <= i < arr.len() && arr[i] == elem
}

spec fn is_sorted(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
}

spec fn has_no_duplicates(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && i != j ==> arr[i] != arr[j]
}

spec fn in_exactly_one(ar1: Seq<i32>, ar2: Seq<i32>, elem: i32) -> bool {
    (contains_element(ar1, elem) && !contains_element(ar2, elem)) ||
    (contains_element(ar2, elem) && !contains_element(ar1, elem))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed type mismatches and slice expressions */
fn contains(arr: &Vec<i32>, x: i32) -> (found: bool)
    ensures
        found <==> contains_element(arr@, x)
{
    let mut i = 0;
    let mut found = false;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            found ==> exists|j: int| 0 <= j < i && arr[j] == x,
            !found ==> forall|j: int| 0 <= j < i ==> arr[j] != x
    {
        if arr[i] == x {
            found = true;
        }
        i += 1;
    }
    found
}

fn sort_and_dedup(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        is_sorted(result@),
        has_no_duplicates(result@),
        forall|i: int| 0 <= i < result.len() ==> contains_element(arr@, result[i]),
        forall|x: i32| contains_element(arr@, x) ==> contains_element(result@, x)
{
    let mut distinct = Vec::new();
    for i in 0..arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < distinct.len() ==> contains_element(arr@.subrange(0, i), distinct[j]),
            forall|j: int| 0 <= j < i ==> contains_element(distinct@, arr[j])
    {
        if !contains(&distinct, arr[i]) {
            distinct.push(arr[i]);
        }
    }
    let mut sorted = distinct;
    for i in 1..sorted.len()
        invariant
            is_sorted(sorted@.subrange(0, i)),
            sorted@.subrange(0, i).to_set() == distinct@.subrange(0, i).to_set()
    {
        let mut j = i;
        while j > 0 && sorted[j-1] > sorted[j]
            invariant
                j >= 0,
                is_sorted(sorted@.subrange(0, j)),
                is_sorted(sorted@.subrange(j, i+1)),
                sorted@.subrange(0, i+1).to_set() == distinct@.subrange(0, i+1).to_set()
            decreases j
        {
            sorted.swap(j, j-1);
            j -= 1;
        }
    }
    sorted
}
// </vc-helpers>

// <vc-spec>
fn numpy_setxor1d(ar1: &Vec<i32>, ar2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        /* Result is sorted */
        is_sorted(result@),
        /* Result has no duplicates */
        has_no_duplicates(result@),
        /* Every element in result is from exactly one input array */
        forall|i: int| 0 <= i < result.len() ==> #[trigger] in_exactly_one(ar1@, ar2@, result[i]),
        /* Every element that appears in exactly one input array is in the result */
        forall|x: i32| in_exactly_one(ar1@, ar2@, x) ==> contains_element(result@, x)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): No changes needed, helpers fixed */
{
    let union = {
        let mut u = Vec::new();
        u.extend(ar1.iter());
        u.extend(ar2.iter());
        u
    };
    let union_sorted_distinct = sort_and_dedup(&union);
    let mut result = Vec::new();
    for i in 0..union_sorted_distinct.len()
        invariant
            is_sorted(result@),
            has_no_duplicates(result@),
            forall|j: int| 0 <= j < result.len() ==> 
                (exists|k: int| 0 <= k < i && union_sorted_distinct@[k] == result[j]) && 
                in_exactly_one(ar1@, ar2@, result[j]),
            forall|k: int| 0 <= k < i && in_exactly_one(ar1@, ar2@, union_sorted_distinct@[k]) ==> 
                contains_element(result@, union_sorted_distinct@[k])
    {
        let x = union_sorted_distinct[i];
        let found1 = contains(ar1, x);
        let found2 = contains(ar2, x);
        if found1 != found2 {
            result.push(x);
        }
    }
    result
}
// </vc-code>


}
fn main() {}