use vstd::prelude::*;

verus! {

// <vc-helpers>
use vstd::prelude::*;

#[verifier(external_body)]
#[cfg(target_arch = "x86_64")]
pub fn v_min(a: u32, b: u32) -> u32 {
    if a < b { a } else { b }
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
    let mut smallest_even: u32 = 0;
    let mut smallest_even_index: u32 = 0;
    let mut found_even: bool = false;

    let nodes_len = nodes@.len();

    if nodes_len == 0 {
        return Vec::new();
    }

    let mut i: u32 = 0;
    while (i as int) < nodes_len
        invariant
            0 <= i as int && i as int <= nodes_len,
            nodes_len == nodes@.len(),
            found_even == false ==> forall|k: int| 0 <= k < i as int ==> nodes@[k] % 2 != 0,
            found_even == true ==> {
                &&& smallest_even % 2 == 0
                &&& 0 <= smallest_even_index as int && smallest_even_index as int < i as int
                &&& nodes@[smallest_even_index as int] == smallest_even
                &&& forall|k: int| 0 <= k < i as int && nodes@[k] % 2 == 0 ==> smallest_even <= nodes@[k]
                &&& forall|k: int| 0 <= k < smallest_even_index as int ==> nodes@[k] % 2 != 0 || (nodes@[k] % 2 == 0 && nodes@[k] > smallest_even)
            },
    {
        let node_val = nodes@[i as int];
        if node_val % 2 == 0 {
            if !found_even {
                smallest_even = node_val;
                smallest_even_index = i;
                found_even = true;
            } else {
                if node_val < smallest_even {
                    smallest_even = node_val;
                    smallest_even_index = i;
                } else if node_val == smallest_even {
                    smallest_even_index = v_min(smallest_even_index, i);
                }
            }
        }
        i = i + 1;
    }

    if found_even {
        let mut result_vec = vec![0, 0];
        result_vec.set(0, smallest_even);
        result_vec.set(1, smallest_even_index);
        result_vec
    } else {
        Vec::new()
    }
}
// </vc-code>

fn main() {}
}