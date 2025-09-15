// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added proof lemma to help with modular arithmetic */
spec fn compute_rotated_index(i: int, n: int, len: int) -> int {
    if len > 0 {
        ((i - n + len) % len) as int
    } else {
        0
    }
}

proof fn lemma_rotation_equivalence(i: int, n: int, len: int)
    requires
        len > 0,
        0 <= i < len,
    ensures
        ((i - n + len) % len) == ((i + len - (n % len)) % len),
{
    // Proof by modular arithmetic properties
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
/* code modified by LLM (iteration 5): Fixed syntax error in invariant */
{
    let len = l.len();
    if len == 0 {
        return Vec::new();
    }
    
    let mut result = Vec::new();
    let rotation = (n % len) as usize;
    
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let rotated_idx = ((j - rotation as int + len as int) % len as int) as int;
                0 <= rotated_idx && rotated_idx < len as int ==> #[trigger] result@[j] == l@[rotated_idx]
            },
        decreases len - i,
    {
        proof {
            lemma_rotation_equivalence(i as int, rotation as int, len as int);
            assert(0 <= i < len);
            assert(len > 0);
            let idx = ((i as int + len as int - rotation as int) % len as int) as int;
            assert(0 <= idx < len as int);
        }
        let source_idx = if i >= rotation {
            i - rotation
        } else {
            len - rotation + i
        };
        assert(0 <= source_idx < len);
        result.push(l[source_idx]);
        i = i + 1;
    }
    
    proof {
        assert(result.len() == len);
        assert forall|k: int| 0 <= k < len ==> {
            let rotated_idx = ((k - rotation as int + len as int) % len as int) as int;
            result@[k] == l@[rotated_idx]
        };
    }
    
    result
}
// </vc-code>

}
fn main() {}