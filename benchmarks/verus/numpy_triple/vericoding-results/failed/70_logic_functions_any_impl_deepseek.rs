// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed while loop syntax in proof mode */
proof fn all_zero_implies_false(v: Vec<f32>) 
    ensures 
        forall|i: int| 0 <= i < v.len() ==> v[i] == 0.0f32 ==> !(exists|j: int| 0 <= j < v.len() && v[j] != 0.0f32)
{
    if v.len() > 0 {
        let mut i: int = 0;
        
        proof {
            let mut i_spec: int = 0;
            assert(forall|j: int| 0 <= j < i_spec ==> v[j] == 0.0f32);
            assert(!(exists|j: int| 0 <= j < i_spec && v[j] != 0.0f32));
            
            while i_spec < v.len()
                invariant 
                    0 <= i_spec <= v.len(),
                    forall|j: int| 0 <= j < i_spec ==> v[j] == 0.0f32,
                    !(exists|j: int| 0 <= j < i_spec && v[j] != 0.0f32)
                decreases v.len() - i_spec
            {
                assert(v[i_spec] == 0.0f32);
                i_spec = i_spec + 1;
            }
        }
    }
}

proof fn exists_non_zero_implies_true(v: Vec<f32>, idx: int) 
    requires 
        0 <= idx < v.len(),
        v[idx] != 0.0f32
    ensures 
        exists|i: int| 0 <= i < v.len() && v[i] != 0.0f32
{
    assert(v[idx] != 0.0f32);
}

proof fn empty_vec_implies_false(v: Vec<f32>)
    ensures 
        v.len() == 0 ==> !(exists|i: int| 0 <= i < v.len() && v[i] != 0.0f32)
{
}

proof fn result_mutually_exclusive(v: Vec<f32>, result: bool)
    ensures 
        !(result == true && result == false)
{
}
// </vc-helpers>

// <vc-spec>
fn any(v: Vec<f32>) -> (result: bool)
    ensures 
        (result == true <==> exists|i: int| 0 <= i < v.len() && v[i] != 0.0f32) &&
        (result == false <==> forall|i: int| 0 <= i < v.len() ==> v[i] == 0.0f32) &&
        (v.len() == 0 ==> result == false) &&
        (forall|i: int| 0 <= i < v.len() ==> v[i] == 0.0f32 ==> result == false) &&
        (exists|i: int| 0 <= i < v.len() && v[i] != 0.0f32 ==> result == true) &&
        (result == true || result == false) &&
        !(result == true && result == false)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed sequence indexing syntax */
{
    if v.len() == 0 {
        false
    } else {
        let mut found = false;
        let mut idx: usize = 0;
        
        while idx < v.len()
            invariant 
                0 <= idx <= v.len(),
                found == (exists|i: int| 0 <= i < idx && v[i] != 0.0f32),
                !found ==> forall|i: int| 0 <= i < idx ==> v[i] == 0.0f32
            decreases v.len() - idx
        {
            if v[idx] != 0.0f32 {
                found = true;
                break;
            }
            proof {
                assert(v[idx as int] == 0.0f32);
            }
            idx = idx + 1;
        }
        
        found
    }
}
// </vc-code>

}
fn main() {}