// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed function signatures to match usage */
fn compute_coeff_for_m(scl: i8, m: usize, i: usize) -> i8
    requires
        m == 1 || m == 2,
        i < 100,
        scl.abs() <= 10,
    ensures
        m == 1 ==> (result as int) == (scl as int) * (2 * ((i + 1) as int)),
        m == 2 ==> (result as int) == (scl as int) * (scl as int) * (2 * ((i + 2) as int)) * (2 * ((i + 1) as int)),
{
    if m == 1 {
        let calc = (scl as i32) * 2 * ((i + 1) as i32);
        #[verifier::truncate] (calc as i8)
    } else if m == 2 {
        let calc = (scl as i32) * (scl as i32) * 2 * ((i + 2) as i32) * 2 * ((i + 1) as i32);
        #[verifier::truncate] (calc as i8)
    } else {
        scl
    }
}

fn safe_multiply_i8(a: i8, b: i32) -> (result: i8)
    ensures
        (result as int) == (a as int) * (b as int),
{
    #[verifier::truncate] ((a as i32) * b as i8)
}
// </vc-helpers>

// <vc-spec>
fn hermder(c: Vec<i8>, m: usize, scl: i8) -> (result: Vec<i8>)
    ensures
        result.len() == if m >= c.len() { 0 } else { c.len() - m },
        m >= c.len() ==> result.len() == 0,
        m < c.len() ==> result.len() == c.len() - m,
        (m == 1 && c.len() > 0) ==> (
            forall|i: int| 0 <= i < result.len() ==> 
                result[i] as int == (scl as int) * (2 * ((i + 1) as int)) * (c[i + 1] as int)
        ),
        (m == 2 && c.len() > 1) ==> (
            forall|i: int| 0 <= i < result.len() ==>
                result[i] as int == (scl as int) * (scl as int) * (2 * ((i + 2) as int)) * (2 * ((i + 1) as int)) * (c[i + 2] as int)
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed variable scope issues and postcondition references */
    if m >= c.len() {
        return Vec::new();
    }
    
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < c.len() - m
        invariant
            result.len() == i,
            i <= c.len() - m,
            m < c.len(),
            (m == 1 && c.len() > 0) ==> (
                forall|j: int| 0 <= j < i ==> 
                    result[j] as int == (scl as int) * (2 * ((j + 1) as int)) * (c[j + 1] as int)
            ),
            (m == 2 && c.len() > 1) ==> (
                forall|j: int| 0 <= j < i ==> 
                    result[j] as int == (scl as int) * (scl as int) * (2 * ((j + 2) as int)) * (2 * ((j + 1) as int)) * (c[j + 2] as int)
            ),
        decreases c.len() - m - i
    {
        let val = if m == 1 {
            let coeff = (scl as i32) * 2 * ((i + 1) as i32);
            #[verifier::truncate] ((coeff * (c[i + 1] as i32)) as i8)
        } else if m == 2 {
            let coeff = (scl as i32) * (scl as i32) * 2 * ((i + 2) as i32) * 2 * ((i + 1) as i32);
            #[verifier::truncate] ((coeff * (c[i + 2] as i32)) as i8)
        } else {
            #[verifier::truncate] ((scl as i32 * c[i + m] as i32) as i8)
        };
        
        result.push(val);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}