// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn insertion_sort(arr: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result@.len() == arr@.len(),
        result@.to_set() == arr@.to_set(),
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] <= result@[j],
{
    let seq: Seq<i8> = arr.into();
    let sorted_seq = seq.sort();
    sorted_seq.into()
}

fn remove_duplicates_from_sorted(sorted_arr: Vec<i8>) -> (result: Vec<i8>)
    requires
        forall|i: int, j: int| 0 <= i < j < sorted_arr@.len() ==> sorted_arr@[i] <= sorted_arr@[j],
    ensures
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] < result@[j],
        result@.to_set() == sorted_arr@.to_set(),
        forall|i: int| 0 <= i < sorted_arr@.len() ==> exists|j: int| 0 <= j < result@.len() && sorted_arr@[i] == result@[j],
{
    let n = sorted_arr.len();
    if n == 0 {
        return Vec::new();
    }
    let mut result = Vec::new();
    result.push(sorted_arr[0]);
    let mut last = sorted_arr[0];
    for i in 1..n
        invariant
            1 <= i <= n,
            result.len() >= 1,
            forall|k: int| 1 <= k < result.len() ==> result[k-1] < result[k],
            forall|k: int| 0 <= k < i ==> exists|j: int| 0 <= j < result.len() && sorted_arr[k] == result[j],
    {
        let current = sorted_arr[i];
        if current != last {
            result.push(current);
            last = current;
        }
    }
    result
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
    let sorted_arr = insertion_sort(arr);
    let result = remove_duplicates_from_sorted(sorted_arr);
    result
}
// </vc-code>

}
fn main() {}