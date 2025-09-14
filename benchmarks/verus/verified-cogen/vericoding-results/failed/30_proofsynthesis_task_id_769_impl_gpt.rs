// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): provide a simple spec alias for contains to avoid executable helpers with loops */
spec fn contains_vec(v: &Vec<i32>, x: i32) -> bool { v@.contains(x) }
// </vc-helpers>

// <vc-spec>
fn difference(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)

    ensures
        forall|i: int|
            0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(
                arr1[i],
            )),
        forall|i: int|
            0 <= i < arr2.len() ==> (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(
                arr2[i],
            )),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement set difference via scans with loop invariants and preserve uniqueness */
    let mut result: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < arr1.len()
        invariant i <= arr1.len()
        invariant forall|k: int| 0 <= k < i as int ==> (!arr2@.contains(#[trigger] arr1@[k]) ==> result@.contains(arr1@[k]))
        invariant forall|p: int, q: int| 0 <= p < q < result.len() as int ==> #[trigger] result[p] != #[trigger] result[q]
        decreases arr1.len() - i
    {
        let x = arr1[i];

        // compute membership of x in arr2
        let mut j: usize = 0;
        let mut in_arr2: bool = false;
        while j < arr2.len()
            invariant j <= arr2.len()
            invariant in_arr2 ==> exists|k: int| 0 <= k < j as int && arr2@[k] == x
            invariant !in_arr2 ==> forall|k: int| 0 <= k < j as int ==> arr2@[k] != x
            decreases arr2.len() - j
        {
            if arr2[j] == x { in_arr2 = true; }
            j = j + 1;
        }
        proof {
            if in_arr2 { assert(arr2@.contains(x)); } else { assert(!arr2@.contains(x)); }
        }

        // compute membership of x in result
        let mut t: usize = 0;
        let mut in_res: bool = false;
        while t < result.len()
            invariant t <= result.len()
            invariant in_res ==> exists|k: int| 0 <= k < t as int && result@[k] == x
            invariant !in_res ==> forall|k: int| 0 <= k < t as int ==> result@[k] != x
            decreases result.len() - t
        {
            if result[t] == x { in_res = true; }
            t = t + 1;
        }
        if !in_res {
            proof { assert(forall|k: int| 0 <= k < result.len() as int ==> result@[k] != x); }
        } else {
            proof { assert(result@.contains(x)); }
        }

        if !in_arr2 && !in_res {
            result.push(x);
        }

        i = i + 1;
    }

    let mut j: usize = 0;
    while j < arr2.len()
        invariant j <= arr2.len()
        invariant forall|k: int| 0 <= k < arr1.len() as int ==> (!arr2@.contains(#[trigger] arr1@[k]) ==> result@.contains(arr1@[k]))
        invariant forall|k: int| 0 <= k < j as int ==> (!arr1@.contains(#[trigger] arr2@[k]) ==> result@.contains(arr2@[k]))
        invariant forall|p: int, q: int| 0 <= p < q < result.len() as int ==> #[trigger] result[p] != #[trigger] result[q]
        decreases arr2.len() - j
    {
        let y = arr2[j];

        // compute membership of y in arr1
        let mut i1: usize = 0;
        let mut in_arr1: bool = false;
        while i1 < arr1.len()
            invariant i1 <= arr1.len()
            invariant in_arr1 ==> exists|k: int| 0 <= k < i1 as int && arr1@[k] == y
            invariant !in_arr1 ==> forall|k: int| 0 <= k < i1 as int ==> arr1@[k] != y
            decreases arr1.len() - i1
        {
            if arr1[i1] == y { in_arr1 = true; }
            i1 = i1 + 1;
        }
        proof {
            if in_arr1 { assert(arr1@.contains(y)); } else { assert(!arr1@.contains(y)); }
        }

        // compute membership of y in result
        let mut t2: usize = 0;
        let mut in_res2: bool = false;
        while t2 < result.len()
            invariant t2 <= result.len()
            invariant in_res2 ==> exists|k: int| 0 <= k < t2 as int && result@[k] == y
            invariant !in_res2 ==> forall|k: int| 0 <= k < t2 as int ==> result@[k] != y
            decreases result.len() - t2
        {
            if result[t2] == y { in_res2 = true; }
            t2 = t2 + 1;
        }
        if !in_res2 {
            proof { assert(forall|k: int| 0 <= k < result.len() as int ==> result@[k] != y); }
        } else {
            proof { assert(result@.contains(y)); }
        }

        if !in_arr1 && !in_res2 {
            result.push(y);
        }

        j = j + 1;
    }

    result
}
// </vc-code>

}
fn main() {}