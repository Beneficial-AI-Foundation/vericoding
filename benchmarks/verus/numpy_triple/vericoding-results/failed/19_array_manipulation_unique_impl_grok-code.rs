// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed ensures to use &mut v@ for to_multiset methods */
fn is_sorted_exec(v: &[i32]) -> bool {
    for i in 0..v.len() - 1 {
        if v[i] > v[i + 1] {
            return false;
        }
    }
    true
}

/* helper modified by LLM (iteration 4): Fixed type annotation for old and removed has_no_duplicates from ensures as bubble sort does not guarantee no_duplicates */
fn sort_vec(v: &mut Vec<i32>)
    ensures
        is_sorted(v@),
        old::<Seq<i32>>(&mut v@).to_multiset() == (&mut v@).to_multiset(),
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|k: int, l: int| 0 <= k < l < (v.len() - i) ==> v@[k] <= v@[l],
        decreases v.len() - i
    {
        let mut j = 0;
        while j < v.len() - 1 - i
            invariant
                0 <= j <= v.len() - i - 1,
                forall|k: int| (0 <= k < j + 1) ==> v@[v.len() - 1 - i] >= v@[k],
            decreases v.len() - i - 1 - j
        {
            if v[j] > v[j + 1] {
                v.swap(j, j + 1);
            }
            j += 1;
        }
        i += 1;
    }
}
// </vc-helpers>

// <vc-spec>
spec fn is_sorted(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
}

spec fn has_no_duplicates(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && i != j ==> arr[i] != arr[j]
}

spec fn all_elements_from_input(result: Seq<i32>, input: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < result.len() ==> #[trigger] input.contains(result[i])
}

spec fn all_distinct_elements_present(input: Seq<i32>, result: Seq<i32>) -> bool {
    forall|val: i32| input.contains(val) ==> #[trigger] result.contains(val)
}

fn numpy_unique(arr: Vec<i32>) -> (result: (usize, Vec<i32>))
    ensures
        is_sorted(result.1@),
        has_no_duplicates(result.1@),
        all_elements_from_input(result.1@, arr@),
        all_distinct_elements_present(arr@, result.1@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Removed invalid @ operators on spec Set variables in invariants and assertions */
{
    let mut result_vec = Vec::<i32>::new();
    let mut seen = vstd::set::Set::<i32>::empty();
    let mut i: usize = 0;
    let len = arr.len();
    while i < len
        invariant
            0 <= i <= len,
            seen == (arr@.subrange(0, i as int)).to_set(),
            result_vec@.to_set() == seen,
            has_no_duplicates(result_vec@),
            forall|k: int| 0 <= k < result_vec.len() ==> #[trigger] arr@.contains(result_vec@[k]),
        decreases len - i
    {
        if !seen.contains(arr[i]) {
            seen.insert(arr[i]);
            result_vec.push(arr[i]);
        }
        i += 1;
    }
    sort_vec(&mut result_vec);
    proof {
        assert(seen == arr@.to_set());
    }
    (result_vec.len(), result_vec)
}
// </vc-code>


}
fn main() {}