// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added decreases clause to fix compilation error */
fn is_in_both(x: i32, list1: &Vec<i32>, list2: &Vec<i32>) -> (result: bool)
    ensures
        result == (list1@.contains(x) && list2@.contains(x)),
{
    let mut found_in_list1 = false;
    let mut found_in_list2 = false;
    
    let mut i = 0;
    while i < list1.len()
        invariant
            0 <= i <= list1.len(),
            found_in_list1 == exists|k: int| 0 <= k < i && list1[k] == x,
        decreases list1.len() - i
    {
        if list1[i] == x {
            found_in_list1 = true;
        }
        i += 1;
    }
    
    let mut j = 0;
    while j < list2.len()
        invariant
            0 <= j <= list2.len(),
            found_in_list2 == exists|k: int| 0 <= k < j && list2[k] == x,
        decreases list2.len() - j
    {
        if list2[j] == x {
            found_in_list2 = true;
        }
        j += 1;
    }
    
    found_in_list1 && found_in_list2
}
// </vc-helpers>

// <vc-spec>
fn shared_elements(list1: &Vec<i32>, list2: &Vec<i32>) -> (shared: Vec<i32>)

    ensures
        forall|i: int|
            0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                #[trigger] shared[i],
            )),
        forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added decreases clauses to fix compilation error */
    let mut shared = Vec::new();
    let mut i = 0;
    while i < list1.len()
        invariant
            0 <= i <= list1.len(),
            forall|k: int| 0 <= k < shared.len() ==> (list1@.contains(shared[k]) && list2@.contains(shared[k])),
            forall|k1: int, k2: int| 0 <= k1 < k2 < shared.len() ==> shared[k1] != shared[k2],
        decreases list1.len() - i
    {
        let elem = list1[i];
        if is_in_both(elem, list1, list2) {
            let mut already_added = false;
            let mut j = 0;
            while j < shared.len()
                invariant
                    0 <= j <= shared.len(),
                    already_added == exists|k: int| 0 <= k < j && shared[k] == elem,
                decreases shared.len() - j
            {
                if shared[j] == elem {
                    already_added = true;
                    break;
                }
                j += 1;
            }
            if !already_added {
                shared.push(elem);
            }
        }
        i += 1;
    }
    shared
}
// </vc-code>

}
fn main() {}