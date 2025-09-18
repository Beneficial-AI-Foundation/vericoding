// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate to check membership */
spec fn vec_contains(v: Vec<i32>, x: i32) -> bool {
    exists|i: int| 0 <= i < v.len() && v@[i] == x
}

/* helper modified by LLM (iteration 5): predicate for sortedness */
spec fn is_sorted(v: Vec<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> v@[i] < v@[j]
}

/* helper modified by LLM (iteration 5): predicate for uniqueness */
spec fn is_unique(v: Vec<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < v.len() && 0 <= j < v.len() && i != j ==> v@[i] != v@[j]
}
// </vc-helpers>

// <vc-spec>
fn unique(arr: Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| #![trigger result[i], result[j]] 0 <= i < j < result.len() ==> result[i] < result[j],

        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> exists|j: int| 0 <= j < arr.len() && result[i] == arr[j],

        forall|i: int, j: int| #![trigger result[i], result[j]] 0 <= i < result.len() && 0 <= j < result.len() && i != j ==> result[i] != result[j],

        forall|i: int| #![trigger arr[i]] 0 <= i < arr.len() ==> exists|j: int| 0 <= j < result.len() && arr[i] == result[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build sorted unique vector by inserting elements in order */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant forall|p: int, q: int| 0 <= p < q < (result.len() as int) ==> result@[p] < result@[q],
        invariant forall|p: int| 0 <= p < (result.len() as int) ==> exists|j: int| 0 <= j < (i as int) && result@[p] == arr@[j],
        invariant forall|k: int| 0 <= k < (i as int) ==> exists|j: int| 0 <= j < (result.len() as int) && arr@[k] == result@[j],
        decreases arr.len() - i
    {
        let x = arr[i];
        let mut found: bool = false;
        let mut j: usize = 0;
        while j < result.len()
            invariant !found ==> (forall|t: int| 0 <= t < (j as int) ==> result@[t] != x),
            decreases result.len() - j
        {
            if result[j] == x {
                found = true;
                break;
            }
            j += 1;
        }
        if !found {
            let mut pos: usize = 0;
            while pos < result.len() && result[pos] < x
                invariant forall|t: int| 0 <= t < (pos as int) ==> result@[t] < x,
                decreases result.len() - pos
            {
                pos += 1;
            }
            result.insert(pos, x);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}