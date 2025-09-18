// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix type conversion from usize to int in proof context */
proof fn rotation_proof(l: Seq<i32>, n: usize, i: usize, len: usize)
    requires
        len > 0,
        n < len,
        i < len,
    ensures
        ((i as int - n as int + len as int) % len as int) == mod_index(i as int - n as int, len as int),
{
    let rotated_index = mod_index(i as int - n as int, len as int);
    assert(0 <= rotated_index < len as int);
}

spec fn mod_index(i: int, len: int) -> (r: int)
    requires
        len > 0,
    ensures
        0 <= r < len,
        r == i % len,
{
    if i >= 0 {
        i % len
    } else {
        (i % len + len) % len
    }
}
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
/* code modified by LLM (iteration 5): Fix int conversion issues by casting to usize in execution context */
{
    let len = l.len();
    if len == 0 {
        Vec::empty()
    } else {
        let mut result = Vec::with_capacity(len);
        let n_mod = n % len;
        
        for i in 0..len {
            proof {
                rotation_proof(l@, n_mod, i, len);
            }
            let rotated_index_int = mod_index(i as int - n_mod as int, len as int);
            let rotated_index = rotated_index_int as usize;
            result.push(l[rotated_index]);
        }
        
        result
    }
}
// </vc-code>

}
fn main() {}