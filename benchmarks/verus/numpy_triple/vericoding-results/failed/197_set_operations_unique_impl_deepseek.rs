// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix Seq indexing syntax */
fn sorted(arr: Seq<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
}

fn sorted_strict(arr: Seq<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] < arr[j]
}

fn contains<T>(seq: Seq<T>, elem: T) -> bool {
    exists|i: int| 0 <= i < seq.len() && seq[i] == elem
}

proof fn lemma_sorted_unique(arr: Seq<i8>)
    requires
        sorted(arr),
    ensures
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && i != j ==> arr[i] != arr[j],
{
    assert forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && i != j implies arr[i] != arr[j] by {
        if i < j {
            assert(arr[i] <= arr[j]);
            assert(arr[i] != arr[j]);
        } else {
            assert(j < i);
            assert(arr[j] <= arr[i]);
            assert(arr[j] != arr[i]);
        }
    };
}

fn insert_sorted(elem: i8, arr: Vec<i8>) -> (result: Vec<i8>)
    requires
        sorted(arr@),
    ensures
        sorted(result@),
        contains(result@, elem),
        forall|e| contains(result@, e) ==> contains(arr@, e) || e == elem,
        result@.len() == arr@.len() + 1,
{
    let mut i = 0;
    let mut new_arr = Vec::new();
    
    while i < arr.len()
        invariant
            sorted(new_arr@),
            new_arr@.len() == i,
            forall|j: int| 0 <= j < i ==> arr@[j] == new_arr@[j],
        decreases arr.len() - i,
    {
        if arr[i] >= elem {
            new_arr.push(elem);
            new_arr.push(arr[i]);
        } else {
            new_arr.push(arr[i]);
        }
        i += 1;
    }
    
    if new_arr.len() == arr.len() {
        new_arr.push(elem);
    }
    
    new_arr
}
// </vc-helpers>

// <vc-spec>
fn unique(arr: Vec<i8>) -> (result: Vec<i8>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result@.len() ==> #[trigger] result@[i] < #[trigger] result@[j],

        forall|i: int| 0 <= i < result@.len() ==> exists|j: int| 0 <= j < arr@.len() && #[trigger] result@[i] == #[trigger] arr@[j],

        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@.len() && i != j ==> #[trigger] result@[i] != #[trigger] result@[j],

        forall|i: int| 0 <= i < arr@.len() ==> exists|j: int| 0 <= j < result@.len() && #[trigger] arr@[i] == #[trigger] result@[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix Seq indexing syntax and verification */
    let mut sorted_arr = Vec::new();
    
    let mut i = 0;
    while i < arr.len()
        invariant
            sorted(sorted_arr@),
            forall|e| contains(sorted_arr@, e) ==> exists|j: int| 0 <= j < arr@.len() && arr@[j] == e,
            forall|j: int| 0 <= j < arr@.len() ==> contains(sorted_arr@, arr@[j]),
        decreases arr.len() - i,
    {
        sorted_arr = insert_sorted(arr[i], sorted_arr);
        i += 1;
    }
    
    lemma_sorted_unique(sorted_arr@);
    
    let mut result = Vec::new();
    let mut prev: Option<i8> = None;
    let mut j = 0;
    
    while j < sorted_arr.len()
        invariant
            sorted_strict(result@),
            forall|e| contains(result@, e) ==> contains(sorted_arr@, e),
            forall|k: int| 0 <= k < sorted_arr@.len() ==> contains(sorted_arr@, sorted_arr@[k]),
        decreases sorted_arr.len() - j,
    {
        let current = sorted_arr[j];
        if prev.is_none() || prev.unwrap() < current {
            result.push(current);
            prev = Some(current);
        }
        j += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}