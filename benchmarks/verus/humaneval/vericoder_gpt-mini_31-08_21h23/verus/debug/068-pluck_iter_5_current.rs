use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed
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
    let n = nodes.len();
    let mut i: usize = 0;
    let mut found: bool = false;
    let mut best_val: u32 = 0;
    let mut best_index: usize = 0;

    while i < n {
        invariant i <= n;
        invariant (!found) ==> forall|j: int| 0 <= j && j < (i as int) ==> nodes@[j] % 2 != 0;
        invariant found ==> 0 <= (best_index as int) && (best_index as int) < (i as int);
        invariant found ==> nodes@[(best_index as int)] == best_val;
        invariant found ==> best_val % 2 == 0;
        invariant found ==> forall|j: int| 0 <= j && j < (i as int) && nodes@[j] % 2 == 0 ==> best_val <= nodes@[j];
        invariant found ==> forall|j: int| 0 <= j && j < (best_index as int) ==> nodes@[j] % 2 != 0 || nodes@[j] > best_val;
        decreases (n as int) - (i as int);
        {
            let v: u32 = nodes[i];
            if v % 2 == 0 {
                if !found {
                    found = true;
                    best_val = v;
                    best_index = i;
                } else {
                    if v < best_val {
                        // update to new smaller even at a later index
                        best_val = v;
                        best_index = i;
                    }
                }
            }
            i += 1;
        }
    }

    if !found {
        proof {
            // At loop exit i == n and (!found) implies every seen element (all elements) are odd
            assert(i == n);
            assert(!found);
            assert(forall|j: int| 0 <= j && j < (i as int) ==> nodes@[j] % 2 != 0);
        }
        vec![]
    } else {
        proof {
            // At loop exit i == n and invariants give required properties about best_val and best_index
            assert(i == n);
            assert(found);
            assert(0 <= (best_index as int) && (best_index as int) < (i as int));
            assert(nodes@[(best_index as int)] == best_val);
            assert(best_val % 2 == 0);
            assert(forall|j: int| 0 <= j && j < (i as int) && nodes@[j] % 2 == 0 ==> best_val <= nodes@[j]);
            assert(forall|j: int| 0 <= j && j < (best_index as int) ==> nodes@[j] % 2 != 0 || nodes@[j] > best_val);
        }
        vec![best_val, best_index as u32]
    }
}
// </vc-code>

fn main() {}
}