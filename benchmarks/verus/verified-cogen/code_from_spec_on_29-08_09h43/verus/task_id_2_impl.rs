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
        decreases arr.len() - i
    {
        if (arr[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

fn contains_unique(shared: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < shared.len() && shared[i] == key),
{
    let mut i = 0;
    while i < shared.len()
        invariant
            forall|m: int| 0 <= m < i ==> (shared[m] != key),
        decreases shared.len() - i
    {
        if (shared[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

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
{
    let mut shared = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 2): added decreases clause to fix verification error */
    while i < list1.len()
        invariant
            forall|k: int| 0 <= k < shared.len() ==> (list1@.contains(shared[k]) && list2@.contains(shared[k])),
            forall|k: int, j: int| 0 <= k < j < shared.len() ==> shared[k] != shared[j],
        decreases list1.len() - i
    {
        if contains(list2, list1[i]) && !contains_unique(&shared, list1[i]) {
            shared.push(list1[i]);
        }
        i += 1;
    }
    
    shared
}
// </vc-code>

} // verus!

fn main() {}