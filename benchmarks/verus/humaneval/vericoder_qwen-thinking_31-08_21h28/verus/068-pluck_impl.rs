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
{
    let mut min_val: Option<u32> = None;
    let mut min_idx: Option<nat> = None;
    let mut i: nat = 0;
    while i < nodes.len() as nat {
        invariant
            (min_val == None) == (min_idx == None) &&
            (min_val == None) ==>
                (forall |j: nat| 0 <= j && j < i && j < nodes@.len() ==> nodes@[j] % 2 != 0) &&
            (min_val != None) ==>
                (min_idx != None &&
                 min_idx.unwrap() < i &&
                 nodes@[min_idx.unwrap()] == min_val.unwrap() &&
                 min_val.unwrap() % 2 == 0 &&
                 (forall |j: nat| 0 <= j && j < min_idx.unwrap() && j < nodes@.len() ==> nodes@[j] % 2 != 0 || nodes@[j] > min_val.unwrap()) &&
                 (forall |j: nat| min_idx.unwrap() <= j && j < i && j < nodes@.len() ==> nodes@[j] % 2 != 0 || nodes@[j] >= min_val.unwrap()));
        let x = nodes[i as usize];
        if x % 2 == 0 {
            match min_val {
                None => {
                    min_val = Some(x);
                    min_idx = Some(i);
                }
                Some(m) => {
                    if x < m {
                        min_val = Some(x);
                        min_idx = Some(i);
                    }
                }
            }
        }
        i = i + 1;
    }
    if min_val.is_some() {
        vec![min_val.unwrap(), min_idx.unwrap() as u32]
    } else {
        vec![]
    }
}
// </vc-code>

fn main() {}
}