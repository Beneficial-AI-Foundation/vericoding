use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helper lemmas needed.
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
    let n: int = nodes@.len() as int;
    let mut i: int = 0;
    let mut found: bool = false;
    let mut best_val: u32 = 0;
    let mut best_idx: int = 0;

    while i < n
        invariant 0 <= i && i <= n,
        invariant (!found) ==> forall(|j: int| 0 <= j && j < i ==> nodes@[j] % 2 != 0),
        invariant found ==> 0 <= best_idx && best_idx < i,
        invariant found ==> nodes@[best_idx] == best_val,
        invariant found ==> nodes@[best_idx] % 2 == 0,
        invariant found ==> (forall(|j: int| 0 <= j && j < i && nodes@[j] % 2 == 0 ==> #[trigger] best_val <= nodes@[j])),
        invariant found ==> (forall(|j: int| 0 <= j && j < best_idx ==> nodes@[j] % 2 != 0 || #[trigger] nodes@[j] > best_val))
    {
        let v: u32 = nodes[i as usize];
        if v % 2 == 0 {
            if !found || v < best_val {
                best_val = v;
                best_idx = i;
                found = true;
            }
        }
        i += 1;
    }

    if !found {
        // By the loop invariant !found ==> forall j < i: nodes[j] odd, and at loop exit i == n
        proof {
            assert(i == n);
            assert(forall |j: int| 0 <= j && j < n ==> nodes@[j] % 2 != 0);
        }
        Vec::new()
    } else {
        // At loop exit i == n and found holds; use invariants to build result satisfying postconditions
        proof {
            assert(i == n);
            assert(0 <= best_idx && best_idx < n);
            assert(nodes@[best_idx] == best_val);
            assert(nodes@[best_idx] % 2 == 0);
            assert(forall |j: int| 0 <= j && j < n && nodes@[j] % 2 == 0 ==> best_val <= nodes@[j]);
            assert(forall |j: int| 0 <= j && j < best_idx ==> nodes@[j] % 2 != 0 || nodes@[j] > best_val);
        }
        let mut res: Vec<u32> = Vec::new();
        res.push(best_val);
        // safe to cast best_idx to u32 because best_idx >= 0 and nodes@.len() <= u32::MAX (precondition) and best_idx < n
        let idx_u32: u32 = best_idx as u32;
        res.push(idx_u32);
        res
    }
    // impl-end
}
// </vc-code>

fn main() {}
}