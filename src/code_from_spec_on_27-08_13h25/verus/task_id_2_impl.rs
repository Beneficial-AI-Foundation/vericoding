use vstd::prelude::*;

verus! {

// <vc-helpers>
fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            forall|m: int| 0 <= m < i ==> (arr[m] != key),
    {
        if (arr[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

proof fn vec_contains_implies_exists(v: &Vec<i32>, x: i32)
    requires
        v@.contains(x),
    ensures
        exists|i: int| 0 <= i < v.len() && v[i] == x,
{
    let idx = v@.index_of(x);
    assert(0 <= idx < v.len());
    assert(v[idx] == x);
}
// </vc-helpers>

// <vc-spec>
fn shared_elements(list1: &Vec<i32>, list2: &Vec<i32>) -> (shared: Vec<i32>)
    // post-conditions-start
    ensures
        forall|i: int|
            0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                #[trigger] shared[i],
            )),
        forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
    // post-conditions-end
// </vc-spec>

// <vc-code>
fn shared_elements(list1: &Vec<i32>, list2: &Vec<i32>) -> (shared: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                #[trigger] shared[i],
            )),
        forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < list1.len()
        invariant
            forall|k: int| 0 <= k < result.len() ==> (list1@.contains(#[trigger] result[k]) && list2@.contains(#[trigger] result[k])),
            forall|k: int, m: int| 0 <= k < m < result.len() ==> result[k] != result[m],
            forall|k: int| 0 <= k < i ==> !list2@.contains(list1[k]) || (exists|m: int| 0 <= m < result.len() && result[m] == list1[k]),
    {
        let elem = list1[i];
        if list2@.contains(elem) && !result@.contains(elem) {
            result.push(elem);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}