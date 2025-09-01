use vstd::prelude::*;

verus! {

// <vc-helpers>

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
                0 <= i < nodes@.len() && nodes@[i] % 2 == 0 ==> node <= nodes@[i] && forall|k: int|
                    0 <= k < result@[1] ==> nodes@[k] % 2 != 0 || nodes@[k] > node
        },
    // post-conditions-end
{
    #[verifier::loop_isolation(false)]
    let mut i: usize = 0;
    let mut found: bool = false;
    let mut min_val: u32 = 0;
    let mut min_index: usize = 0;
    while i < nodes.len()
        invariant
            0 <= i as int <= nodes@.len(),
            if found {
                &&& min_val % 2 == 0
                &&& 0 <= min_index as int < i as int
                &&& nodes@[min_index as int] == min_val
                &&& forall|j: int| 0 <= j < i as int && nodes@[j] % 2 == 0 ==> min_val <= nodes@[j]
                &&& forall|j: int| 0 <= j < i as int && nodes@[j] % 2 == 0 && nodes@[j] == min_val ==> j == min_index as int
            } else {
                forall|j: int| 0 <= j < i as int ==> nodes@[j] % 2 != 0
            }
    {
        if nodes@[i as int] % 2 == 0 {
            if !found {
                min_val = nodes@[i as int];
                min_index = i;
                found = true;
            } else if nodes@[i as int] < min_val {
                min_val = nodes@[i as int];
                min_index = i;
            }
            // Else, if equal, do nothing to keep the smallest index
        }
        i = i + 1;
    }
    if !found {
        Vec::new()
    } else {
        let result_vec = vec![min_val, min_index as u32];
        proof {
            assert(result_vec@.len() == 2);
            let node = result_vec@[0];
            let index_int = result_vec@[1] as int;
            assert(node == min_val);
            assert(index_int == min_index as int);
            assert(nodes@[index_int] == node);
            assert(node % 2 == 0);
            assert(0 <= index_int < nodes@.len());
            assert forall|j: int| 0 <= j < nodes@.len() && nodes@[j] % 2 == 0 implies node <= nodes@[j] by {
                if nodes@[j] % 2 == 0 {
                    assert(j < nodes@.len());
                    assert(nodes@[j] % 2 == 0);
                    if j >= i as int {
                        // after the loop, but need to check further
                        assert(false); // contradiction in loop invariant but need more proving
                    } else {
                        // from invariant
                    }
                }
            }
            assert forall|k: int| 0 <= k < result_vec@[1] as int implies nodes@[k] % 2 != 0 || nodes@[k] > node by {
                if nodes@[k] % 2 == 0 {
                    if k >= i as int {
                        // similar
                    } else {
                        // from invariant, if equal and same, but k < min_index, contradiction
                        if nodes@[k] < node || nodes@[k] == node {
                            // but from invariant no
                        } else {
                            // fine
                        }
                    }
                }
            }
        }
        result_vec
    }
}
// </vc-code>

fn main() {}
}