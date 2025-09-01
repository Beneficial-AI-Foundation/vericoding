use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn pluck_smallest_even(nodes: &Vec<u32>) -> (result: Vec<u32>)
    // pre-conditions-start
    requires
        nodes@.len() <= u32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result@.len() == 0 || result@.len() == 2,
        result@.len() == 0 ==> forall|i: int| 0 <= i < nodes@.len() ==> nodes@[i] % 2 != 0,
        result@.len() == 2 ==> {
            let node = result@[0];
            let index = result@[1];
            &&& 0 <= index < nodes@.len()
            &&& nodes@[index as int] == node
            &&& node % 2 == 0
            &&& forall|i: int|
                0 <= i < nodes@.len() && nodes@[i] % 2 == 0 ==> node <= nodes@[i] && forall|i: int|
                    0 <= i < result@[1] ==> nodes@[i] % 2 != 0 || nodes@[i] > node
        },
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    #[verifier::loop_isolation(false)]
    let mut i: usize = 0;
    let mut found: bool = false;
    let mut min_val: u32 = 0;
    let mut min_index: usize = 0;
    while i < nodes.len()
        invariant
            0 <= i <= nodes@.len(),
            if found {
                &&& min_val % 2 == 0
                &&& 0 <= min_index < i
                &&& nodes@[min_index] == min_val
                &&& forall|j: int| 0 <= j < i && nodes@[j] % 2 == 0 ==> min_val <= nodes@[j]
                &&& forall|j: int| 0 <= j < i ==> (!(nodes@[j] == min_val) || j >= min_index)
                &&& forall|j: int| 0 <= j < i && nodes@[j] % 2 == 0 && nodes@[j] == min_val ==> j == min_index
            } else {
                forall|j: int| 0 <= j < i ==> nodes@[j] % 2 != 0
            }
    {
        if nodes@[i] % 2 == 0 {
            if !found {
                min_val = nodes@[i];
                min_index = i;
                found = true;
            } else if nodes@[i] < min_val {
                min_val = nodes@[i];
                min_index = i;
            }
            // Else, if equal, do nothing to keep the smallest index
        }
        i = i + 1;
    }
    if !found {
        vec![]
    } else {
        proof {
            assert(result@.len() == 2);
            let node = result@[0] as nat;
            let index = result@[1] as int;
            assert(0 <= index < nodes@.len());
            assert(nodes@[index as nat] == node);
            assert(node % 2 == 0);
            assert(forall|i: int| 0 <= i < nodes@.len() && nodes@[i] % 2 == 0 ==> node <= nodes@[i]);
            assert(forall|i: int| 0 <= i < index ==> nodes@[i] % 2 != 0 || nodes@[i] > node);
        }
        vec![min_val, min_index as u32]
    }
    // impl-end
}
// </vc-code>

fn main() {}
}