// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_index(i: int, len: int) -> bool { 0 <= i < len }

/* helper modified by LLM (iteration 5): changed lemma to proof fn for proper syntax */
proof fn mod_bounds(a: int, b: int)
    requires b > 0
    ensures 0 <= a % b < b
{
}

proof fn rotation_property(i: int, offset: int, len: int)
    requires 0 <= i < len, offset >= 0, len > 0
    ensures 0 <= (i + offset) % len < len
{
    mod_bounds(i + offset, len);
}
// </vc-helpers>

// <vc-spec>
fn rotate(a: &Vec<i32>, offset: int) -> (result: Vec<i32>)
    requires offset >= 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            let src_idx = (i + offset) % (a.len() as int);
            #[trigger] result[i] == a[src_idx]
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use ghost variables for int conversions */
{
    if a.len() == 0 {
        return Vec::new();
    }
    
    let mut result = Vec::with_capacity(a.len());
    ghost let len = a.len() as int;
    
    for i in 0..a.len()
        invariant
            result.len() == i,
            len == a.len(),
            forall|j: int| 0 <= j < i ==> {
                let src_idx = (j + offset) % len;
                result[j] == a[src_idx]
            }
    {
        proof {
            rotation_property(i as int, offset, len);
        }
        ghost let i_int = i as int;
        ghost let src_idx_int = (i_int + offset) % len;
        let src_idx = src_idx_int as usize;
        result.push(a[src_idx]);
    }
    
    result
}
// </vc-code>

}
fn main() {}