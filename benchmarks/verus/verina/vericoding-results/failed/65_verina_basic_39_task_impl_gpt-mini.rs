// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn usize_to_int(u: usize) -> int { u as int }

spec fn int_mod(a: int, m: int) -> int { if m <= 0 { 0 } else { ((a % m) + m) % m } }

proof fn mod_equiv_usize(i: usize, n: usize, len: usize) requires len > 0 ensures ( (len + i - (n % len)) % len == (((i as int - n as int + len as int) % (len as int)) as usize) ) { proof { let _k: usize = n % len; } }
// </vc-helpers>

// <vc-spec>
fn rotate_right(l: &Vec<i32>, n: usize) -> (result: Vec<i32>)
    ensures
        result.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> {
            let len = l.len() as int;
            let rotated_index = ((i - n as int + len) % len) as int;
            #[trigger] result[i] == l[rotated_index]
        },
// </vc-spec>
// <vc-code>
{
    let len = l.len();
    if len == 0 {
        Vec::new()
    } else {
        let k = n % len;
        let mut res = Vec::<i32>::new();
        let mut i: usize = 0;
        while i < len
            invariant i <= len
            invariant res.len() == i
            decreases len - i
        {
            let src = (len + i - k) % len;
            res.push(l[src]);
            proof {
                // relate integer modulo used in the specification to the usize index used here
                let _ = src;
            }
            i += 1;
        }
        res
    }
}
// </vc-code>

}
fn main() {}