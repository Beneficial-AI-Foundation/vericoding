// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed invariant initialization by ensuring proper bounds check and proper postcondition proof */
fn contains(arr: &Vec<i8>, val: i8) -> (result: bool)
    ensures
        result == exists|i: int| 0 <= i < arr@.len() && #[trigger] arr@[i] == val,
{
    for i in 0..arr.len()
        invariant
            forall|j: int| 0 <= j < i ==> #[trigger] arr@[j] != val,
    {
        if arr[i] == val {
            return true;
        }
    }
    false
}

fn insert_sorted(arr: &mut Vec<i8>, val: i8)
    requires
        forall|i: int, j: int| 0 <= i < j < old(arr)@.len() ==> #[trigger] old(arr)@[i] < #[trigger] old(arr)@[j],
    ensures
        arr@.len() == old(arr)@.len() + 1,
        forall|i: int, j: int| 0 <= i < j < arr@.len() ==> #[trigger] arr@[i] < #[trigger] arr@[j],
        exists|k: int| 0 <= k < arr@.len() && #[trigger] arr@[k] == val,
        forall|i: int| 0 <= i < old(arr)@.len() ==> exists|j: int| 0 <= j < arr@.len() && #[trigger] old(arr)@[i] == #[trigger] arr@[j],
{
    let mut pos = 0;
    while pos < arr.len() && arr[pos] < val
        invariant
            0 <= pos <= arr@.len(),
            forall|i: int| 0 <= i < pos ==> #[trigger] arr@[i] < val,
            forall|i: int| pos < i < arr@.len() ==> #[trigger] arr@[i] >= val,
            arr@.len() == old(arr)@.len(),
        decreases arr@.len() - pos
    {
        pos += 1;
    }
    arr.insert(pos, val);
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
    /* code modified by LLM (iteration 5): simplified loop invariants to match postconditions exactly and ensure proper initialization */
    let mut result: Vec<i8> = Vec::new();
    
    for i in 0..arr.len()
        invariant
            forall|x: int, y: int| 0 <= x < y < result@.len() ==> #[trigger] result@[x] < #[trigger] result@[y],
            forall|x: int| 0 <= x < result@.len() ==> exists|y: int| 0 <= y < arr@.len() && #[trigger] result@[x] == #[trigger] arr@[y],
            forall|x: int, y: int| 0 <= x < result@.len() && 0 <= y < result@.len() && x != y ==> #[trigger] result@[x] != #[trigger] result@[y],
            forall|x: int| 0 <= x < i ==> (exists|y: int| 0 <= y < result@.len() && #[trigger] arr@[x] == #[trigger] result@[y]),
    {
        if !contains(&result, arr[i]) {
            insert_sorted(&mut result, arr[i]);
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}