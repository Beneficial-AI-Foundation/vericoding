// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added casts and corrected syntax */
proof fn helper_lemma_m1(c: Seq<i32>, scl: i32, i: int) 
    requires 
        0 <= i < c.len() - 1,
    ensures 
        scl * (2 * ((i + 1) as i32)) * c[i + 1] == scl * (2 * (i as i32 + 1)) * c[i + 1]
{
}

proof fn helper_lemma_m2(c: Seq<i32>, scl: i32, i: int) 
    requires 
        0 <= i < c.len() - 2,
    ensures 
        scl * scl * (2 * ((i + 2) as i32)) * (2 * ((i + 1) as i32)) * c[i + 2] == scl * scl * (2 * (i as i32 + 2)) * (2 * (i as i32 + 1)) * c[i + 2]
{
}

spec fn compute_m1_element(c: Seq<i32>, scl: i32, i: int) -> i32 
    requires 0 <= i < c.len() - 1
{
    scl * (2 * ((i + 1) as i32)) * c[i + 1]
}

spec fn compute_m2_element(c: Seq<i32>, scl: i32, i: int) -> i32 
    requires 0 <= i < c.len() - 2
{
    scl * scl * (2 * ((i + 2) as i32)) * (2 * ((i + 1) as i32)) * c[i + 2]
}

spec fn product_of_factors(i: int, m: int) -> i32
    requires m >= 0
{
    if m == 0 {
        1
    } else {
        (2 * ((i + m) as i32)) * product_of_factors(i, m - 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn hermder(c: Vec<i32>, m: usize, scl: i32) -> (result: Vec<i32>)
    ensures
        result.len() == if m >= c.len() { 0 } else { c.len() - m },
        m >= c.len() ==> result.len() == 0,
        m < c.len() ==> result.len() == c.len() - m,
        (m == 1 && c.len() > 0) ==> (
            forall|i: int| 0 <= i < result.len() ==> 
                result[i] == scl * (2 * ((i + 1) as i32)) * c[i + 1]
        ),
        (m == 2 && c.len() > 1) ==> (
            forall|i: int| 0 <= i < result.len() ==>
                result[i] == scl * scl * (2 * ((i + 2) as i32)) * (2 * ((i + 1) as i32)) * c[i + 2]
        ),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed integer cast syntax */
{
    if m >= c.len() {
        Vec::new()
    } else {
        let mut result = Vec::with_capacity(c.len() - m);
        let mut i: usize = 0;
        
        while i < c.len() - m {
            invariant 
                0 <= i as int <= c.len() as int - m as int,
                result.len() == i,
                forall|j: int| 0 <= j < i ==> {
                    if m == 1 {
                        result@[j] == compute_m1_element(c@, scl, j)
                    } else if m == 2 {
                        result@[j] == compute_m2_element(c@, scl, j)
                    } else {
                        true
                    }
                };
            
            let element = if m == 1 {
                scl * (2 * ((i + 1) as i32)) * c[i + 1]
            } else if m == 2 {
                scl * scl * (2 * ((i + 2) as i32)) * (2 * ((i + 1) as i32)) * c[i + 2]
            } else {
                // General case for m > 2
                let mut value = scl;
                let mut j = 0;
                
                while j < m {
                    invariant 
                        0 <= j as int <= m as int,
                        value == scl.pow(j as u32) * product_of_factors(i as int, j as int);
                    
                    value = value * (2 * ((i + j + 1) as i32));
                    j += 1;
                }
                
                value * c[i + m]
            };
            
            result.push(element);
            i += 1;
        }
        
        result
    }
}
// </vc-code>

}
fn main() {}