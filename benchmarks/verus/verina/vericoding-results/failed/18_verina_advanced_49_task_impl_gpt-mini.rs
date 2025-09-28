// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate spec int-indexed sortedness to usize indices */
proof fn sorted_monotone(arr: &Vec<i32>, i: usize, j: usize)
    requires
        forall|p: int, q: int| 0 <= p < q < arr.len() ==> arr[p] <= arr[q],
        i < j && j < arr.len(),
    ensures
        arr[i] <= arr[j]
{
    proof {
        let pi: int = i as int;
        let pj: int = j as int;
        assert(0 <= pi && pi < pj && pj < arr.len());
        assert(arr[pi] <= arr[pj]);
    }
}
// </vc-helpers>

// <vc-spec>
fn merge_sorted_lists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires 
        forall|i: int, j: int| 0 <= i < j < arr1.len() ==> arr1[i] <= arr1[j],
        forall|i: int, j: int| 0 <= i < j < arr2.len() ==> arr2[i] <= arr2[j],
    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        result.len() == arr1.len() + arr2.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): merged using helper to relate int-spec sortedness to usize indices */
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;

    while i < arr1.len() && j < arr2.len()
        invariant
            i <= arr1.len(),
            j <= arr2.len(),
            res.len() == i + j,
            forall|p: usize, q: usize| p < q && q < res.len() ==> res[p] <= res[q],
            (res.len() == 0) || ((i < arr1.len() ==> arr1[i] >= res[res.len()-1]) && (j < arr2.len() ==> arr2[j] >= res[res.len()-1])),
        decreases arr1.len() + arr2.len() - (i + j)
    {
        if arr1[i] <= arr2[j] {
            res.push(arr1[i]);
            proof {
                if res.len() > 1 {
                    let prev_last = res[res.len()-2];
                    assert(prev_last <= res[res.len()-1]);
                }
                if i + 1 < arr1.len() {
                    sorted_monotone(arr1, i, i+1);
                }
                assert(arr2[j] >= arr1[i]);
            }
            i = i + 1;
        } else {
            res.push(arr2[j]);
            proof {
                if res.len() > 1 {
                    let prev_last = res[res.len()-2];
                    assert(prev_last <= res[res.len()-1]);
                }
                if j + 1 < arr2.len() {
                    sorted_monotone(arr2, j, j+1);
                }
                assert(arr1[i] >= arr2[j]);
            }
            j = j + 1;
        }
    }

    while i < arr1.len()
        invariant
            i <= arr1.len(),
            res.len() == i + j,
            forall|p: usize, q: usize| p < q && q < res.len() ==> res[p] <= res[q],
            (res.len() == 0) || (i < arr1.len() ==> arr1[i] >= res[res.len()-1]),
        decreases arr1.len() - i
    {
        res.push(arr1[i]);
        proof {
            if res.len() > 1 {
                let prev_last = res[res.len()-2];
                assert(prev_last <= res[res.len()-1]);
            }
            if i + 1 < arr1.len() {
                sorted_monotone(arr1, i, i+1);
            }
        }
        i = i + 1;
    }

    while j < arr2.len()
        invariant
            j <= arr2.len(),
            res.len() == i + j,
            forall|p: usize, q: usize| p < q && q < res.len() ==> res[p] <= res[q],
            (res.len() == 0) || (j < arr2.len() ==> arr2[j] >= res[res.len()-1]),
        decreases arr2.len() - j
    {
        res.push(arr2[j]);
        proof {
            if res.len() > 1 {
                let prev_last = res[res.len()-2];
                assert(prev_last <= res[res.len()-1]);
            }
            if j + 1 < arr2.len() {
                sorted_monotone(arr2, j, j+1);
            }
        }
        j = j + 1;
    }

    res
}

// </vc-code>

}
fn main() {}