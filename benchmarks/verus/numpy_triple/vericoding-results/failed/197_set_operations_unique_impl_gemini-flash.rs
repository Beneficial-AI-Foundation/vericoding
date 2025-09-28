// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed a compilation error regarding a missing comma in a `while` loop invariant. */
fn sort(arr: Vec<i8>) -> (res: Vec<i8>) 
    ensures
        (forall |i: int, j: int| 0 <= i < j < res@.len() ==> res@[i] <= res@[j]),
        (forall |v: i8| arr.contains_element(v) == res.contains_element(v)),
        (arr@.len() == res@.len())
{
    let mut arr_mut = arr.clone();
    let len_usize = arr_mut.len();
    let len_int = arr_mut@.len();

    if len_usize == 0 {
        return Vec::new();
    }

    let mut i: usize = 0;
    while i < len_usize
        invariant
            0 <= i as int,
            i as int <= len_int,
            (forall |k: int, l: int| 0 <= k < l < i as int ==> arr_mut@[k] <= arr_mut@[l]),
            (forall |k: int| i as int <= k < len_int ==> (forall |j: int| 0 <= j < i as int ==> arr_mut@[j] <= arr_mut@[k])),
            (forall |v: i8| arr.contains_element(v) == arr_mut.contains_element(v)),
            (arr_mut@.len() == len_int),
        decreases len_usize - i
    {
        let mut min_idx: usize = i;
        let mut j: usize = i + 1;
        while j < len_usize
            invariant
                i as int < j as int,
                j as int <= len_int,
                0 <= min_idx as int,
                min_idx as int < len_int,
                (forall |k: int| i as int <= k < j as int ==> arr_mut@[min_idx as int] <= arr_mut@[k]),
                (forall |v: i8| arr.contains_element(v) == arr_mut.contains_element(v)),
                (arr_mut@.len() == len_int),
            decreases len_usize - j
        {
            if arr_mut@[j as int] < arr_mut@[min_idx as int] {
                min_idx = j;
            }
            j = j + 1;
        }

        let temp = arr_mut.swap(i, min_idx);
        i = i + 1;
    }
    arr_mut
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
/* code modified by LLM (iteration 5): No modification - The previous change was correct. */
{
    let sorted_arr = sort(arr.clone());
    let mut result: Vec<i8> = Vec::new();
    let sorted_arr_len_int = sorted_arr@.len();

    let mut i: usize = 0;
    while i < sorted_arr.len()
        invariant
            0 <= i as int,
            i as int <= sorted_arr_len_int,
            (forall |k: int, l: int| 0 <= k < l < result@.len() ==> result@[k] < result@[l]),
            (forall |k: int| 0 <= k < result@.len() ==> exists|j: int| 0 <= j < arr@.len() && result@[k] == arr@[j]),
            (forall |k: int| 0 <= k < i as int ==> (exists|l: int| 0 <= l < result@.len() && sorted_arr@[k] == result@[l])),
            (forall |k: int| 0 <= k < result@.len() ==> (exists|l: int| 0 <= l < sorted_arr_len_int && result@[k] == sorted_arr@[l])),
        decreases sorted_arr.len() - i
    {
        if i == 0 || (result@.last().is_some() && sorted_arr@[i as int] != result@.last().unwrap()) {
            result.push(sorted_arr@[i as int]);
        }
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}