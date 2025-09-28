// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed contains_index proof function syntax */
predicate! {
    sorted_strictly_ascending(v: &Vec<usize>) -> bool {
        forall|i: int, j: int| 0 <= i < j < v@.len() ==> v@[i] < v@[j]
    }
}

predicate! {
    no_duplicates(v: &Vec<usize>) -> bool {
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() && i != j ==> v@[i] != v@[j]
    }
}

proof fn contains_index(v: Vec<usize>, idx: int) -> (b: bool)
    ensures
        b <==> exists|k: int| 0 <= k < v@.len() && v@[k] == idx,
{
    if exists|k: int| 0 <= k < v@.len() && v@[k] == idx {
        true
    } else {
        false
    }
}
// </vc-helpers>

// <vc-spec>
fn flatnonzero(a: Vec<f64>) -> (result: Vec<usize>)
    ensures

        forall|i: int| 0 <= i < result@.len() ==> a[result@[i] as int] != 0.0,

        forall|j: int| 0 <= j < a@.len() && a@[j] != 0.0 ==> exists|k: int| 0 <= k < result@.len() && result@[k] == j,

        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@.len() && i != j ==> result@[i] != result@[j],

        forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] < result@[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed integer conversions and verification, removed open exists */
    let mut result: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i as int <= a@.len(),
            forall|k: int| 0 <= k < result@.len() ==> a[result@[k] as int] != 0.0,
            forall|j: int| 0 <= j < a@.len() && a@[j] != 0.0 && j < i as int ==> exists|k: int| 0 <= k < result@.len() && result@[k] == j,
            no_duplicates(&result),
            sorted_strictly_ascending(&result),
    {
        if a[i] != 0.0 {
            result.push(i);
            proof {
                assert(a[i] != 0.0);
                assert(result@[result@.len() - 1] == i);
            }
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}