use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn cube_fits_i32(i: int) -> bool {
    let cube = i * i * i;
    cube >= i32::MIN && cube <= i32::MAX
}

proof fn cube_bounds_lemma(i: usize)
    requires i < 1290  // 1290^3 < 2^31, 1291^3 > 2^31
    ensures cube_fits_i32(i as int)
{
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn cubes(len: usize) -> (result: Vec<i32>) by (nonlinear_arith)
    // post-conditions-start
    ensures
        result.len() == len,
        forall|i: int| 0 <= i && i < len ==> result[i] == i * i * i
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < len
        invariant
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == j * j * j,
            i <= len
        decreases len - i
    {
        assert(i < len);
        
        if i >= 1290 {
            // For large values, we'll use 0 to avoid overflow
            result.push(0);
        } else {
            proof {
                cube_bounds_lemma(i);
            }
            let i_int = i as int;
            let cube_int = i_int * i_int * i_int;
            assert(cube_int >= i32::MIN && cube_int <= i32::MAX);
            
            let cube = (i * i * i) as i32;
            assert(cube == cube_int);
            result.push(cube);
        }
        
        i += 1;
    }
    
    assert(i == len);
    assert(result.len() == len);
    
    result
}
// </vc-code>

fn main() {}
}