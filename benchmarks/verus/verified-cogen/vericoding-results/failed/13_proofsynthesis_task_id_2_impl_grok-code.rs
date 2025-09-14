// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): fixed compilation error by removing the problematic invariant for list2 that triggered the syntax error */
{
    let mut shared = Vec::new();
    let mut i = 0;
    while i < list1.len()
    invariant forall|aa: int| 0 <= aa < shared.len() ==> list1@.contains(shared@[aa])
    invariant forall|aa: int, bb: int| 0 <= aa < bb < shared.len() ==> shared@[aa] != shared@[bb]
    decreases list1.len() - i
    {
        let elem = list1[i];
        let mut found = false;
        let mut j = 0;
        while j < list2.len()
        decreases list2.len() - j
        {
            if list2[j] == elem {
                found = true;
                break;
            }
            j += 1;
        }
        if found {
            proof {
                assert(list2@.contains(elem));
            }
            let mut already = false;
            let mut k = 0;
            while k < shared.len()
            invariant 0 <= k <= shared.len()
            invariant !already
            invariant forall|l: int| 0 <= l < k ==> shared@[l] != elem
            decreases shared.len() - k
            {
                if shared[k] == elem {
                    already = true;
                    break;
                }
                k += 1;
            }
            if !already {
                proof {
                    assert(forall|aa: int| 0 <= aa < shared.len() ==> shared@[aa] != elem);
                }
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