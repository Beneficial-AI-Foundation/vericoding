use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_smallest_even_unique(nodes: Seq<u32>, smallest: u32, idx1: int, idx2: int)
    requires
        0 <= idx1 < nodes.len(),
        0 <= idx2 < nodes.len(),
        nodes[idx1] == smallest,
        nodes[idx2] == smallest,
        smallest % 2 == 0,
        forall|i: int| 0 <= i < nodes.len() && nodes[i] % 2 == 0 ==> smallest <= nodes[i],
        forall|i: int| 0 <= i < idx1 ==> nodes[i] % 2 != 0 || nodes[i] > smallest,
        forall|i: int| 0 <= i < idx2 ==> nodes[i] % 2 != 0 || nodes[i] > smallest,
    ensures
        idx1 == idx2
{
    if idx1 != idx2 {
        let min_idx = if idx1 < idx2 { idx1 } else { idx2 };
        let max_idx = if idx1 < idx2 { idx2 } else { idx1 };
        
        assert(nodes[max_idx] == smallest);
        assert(nodes[max_idx] % 2 == 0);
        assert(forall|i: int| 0 <= i < max_idx ==> nodes[i] % 2 != 0 || nodes[i] > smallest);
        assert(nodes[max_idx] > smallest);
        assert(false);
    }
}
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
    let mut smallest_even: Option<u32> = None;
    let mut smallest_index: usize = 0;
    let mut i: usize = 0;
    
    while i < nodes.len()
        invariant
            i <= nodes.len(),
            match smallest_even {
                None => forall|j: int| 0 <= j < i ==> nodes@[j] % 2 != 0,
                Some(val) => {
                    &&& smallest_index < i
                    &&& nodes@[smallest_index as int] == val
                    &&& val % 2 == 0
                    &&& forall|j: int| 0 <= j < i && nodes@[j] % 2 == 0 ==> val <= nodes@[j]
                    &&& forall|j: int| 0 <= j < smallest_index ==> nodes@[j] % 2 != 0 || nodes@[j] > val
                }
            }
        decreases nodes.len() - i
    {
        if nodes[i] % 2 == 0 {
            match smallest_even {
                None => {
                    smallest_even = Some(nodes[i]);
                    smallest_index = i;
                },
                Some(current_smallest) => {
                    if nodes[i] < current_smallest {
                        smallest_even = Some(nodes[i]);
                        smallest_index = i;
                    }
                }
            }
        }
        i += 1;
    }
    
    match smallest_even {
        None => {
            assert(forall|j: int| 0 <= j < nodes@.len() ==> nodes@[j] % 2 != 0);
            vec![]
        },
        Some(val) => {
            let result = vec![val, smallest_index as u32];
            
            proof {
                assert(nodes@[smallest_index as int] == val);
                assert(val % 2 == 0);
                assert(forall|j: int| 0 <= j < nodes@.len() && nodes@[j] % 2 == 0 ==> val <= nodes@[j]);
                assert(forall|j: int| 0 <= j < smallest_index ==> nodes@[j] % 2 != 0 || nodes@[j] > val);
            }
            
            result
        }
    }
}
// </vc-code>

}
fn main() {}