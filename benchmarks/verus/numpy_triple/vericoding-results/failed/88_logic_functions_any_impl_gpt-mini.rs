// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove that vector length is non-negative */
proof fn vec_len_nonneg(v: Vec<f32>)
    ensures
        (v@.len() as int) >= 0,
{
    assert((v@.len() as int) >= 0);
}

// </vc-helpers>

// <vc-spec>
fn any(v: Vec<f32>) -> (result: bool)
    ensures 
        (result == true <==> exists|i: int| 0 <= i < v@.len() && v@[i] != 0.0f32) &&
        (result == false <==> forall|i: int| 0 <= i < v@.len() ==> v@[i] == 0.0f32) &&
        (v@.len() == 0 ==> result == false) &&
        (forall|i: int| 0 <= i < v@.len() ==> v@[i] == 0.0f32 ==> result == false) &&
        (exists|i: int| 0 <= i < v@.len() && v@[i] != 0.0f32 ==> result == true) &&
        (result == true || result == false) &&
        !(result == true && result == false)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use usize indices and maintain invariant connecting found with spec exists over scanned prefix */
    let n: usize = v.len();
    let mut i: usize = 0usize;
    let mut found: bool = false;
    while i < n
        invariant
            0 <= i as int && i as int <= v@.len() as int,
            (found == true <==> exists|j: int| 0 <= j < i as int && v@[j] != 0.0f32),
        decreases n - i
    {
        let val = v.get(i);
        match val {
            Option::Some(x) => {
                if *x != 0.0f32 {
                    found = true;
                }
            }
            Option::None => {}
        }
        i = i + 1usize;
    }
    proof {
        assert(i == n);
        assert(found == (exists|j: int| 0 <= j < n as int && v@[j] != 0.0f32));
    }
    found
}

// </vc-code>

}
fn main() {}