// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min_u32(a: u32, b: u32) -> u32 { if a < b { a } else { b } }
spec fn is_even_u32(x: u32) -> bool { (x as int) % 2 == 0 }
proof fn lemma_trans_le_lt(a: int, b: int, c: int)
    requires
        a <= b,
        b < c,
    ensures
        a < c,
{
}

// </vc-helpers>

// <vc-spec>
fn pluck_smallest_even(nodes: &Vec<u32>) -> (result: Vec<u32>)

    requires
        nodes@.len() <= u32::MAX,

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
// </vc-spec>
// <vc-code>
{
    let n = nodes.len();
    let mut i: usize = 0;
    let mut found: bool = false;
    let mut min_val: u32 = 0;

    while i < n
        invariant
            nodes@.len() == n as int,
            0 <= i as int <= n as int,
            (!found) ==> forall|j: int| 0 <= j < i as int ==> nodes@[j] % 2 != 0,
            found ==> {
                let m = min_val;
                &&& m % 2 == 0
                &&& forall|j: int| 0 <= j < i as int && nodes@[j] % 2 == 0 ==> m <= nodes@[j]
                &&& exists|j: int| 0 <= j < i as int && nodes@[j] == m
            },
        decreases n as int - i as int
    {
        let x = nodes[i];
        if x % 2 == 0 {
            if !found {
                found = true;
                min_val = x;
            } else {
                if x < min_val {
                    min_val = x;
                } else {
                    // keep current min_val
                }
            }
        }
        i += 1;
    }

    if !found {
        Vec::new()
    } else {
        let mut k: usize = 0;
        let mut have_idx: bool = false;
        let mut idx: usize = 0;
        while k < n
            invariant
                nodes@.len() == n as int,
                0 <= k as int <= n as int,
                found,
                have_idx ==> {
                    let di = idx as int;
                    &&& 0 <= di < k as int
                    &&& nodes@[di] == min_val
                    &&& forall|j: int| 0 <= j < di ==> nodes@[j] != min_val
                },
                (!have_idx) ==> forall|j: int| 0 <= j < k as int ==> nodes@[j] != min_val,
                have_idx || exists|j: int| k as int <= j < n as int && nodes@[j] == min_val,
            decreases n as int - k as int
        {
            let y = nodes[k];
            if !have_idx && y == min_val {
                have_idx = true;
                idx = k;
            }
            k += 1;
        }

        let mut res: Vec<u32> = Vec::new();
        res.push(min_val);
        res.push(idx as u32);
        res
    }
}
// </vc-code>

}
fn main() {}