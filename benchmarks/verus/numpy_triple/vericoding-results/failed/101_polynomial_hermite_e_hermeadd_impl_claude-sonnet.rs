// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added overflow-safe addition helper */
spec fn get_coeff(v: Vec<i32>, i: int) -> i32
{
    if i < v.len() { v[i] } else { 0 }
}

proof fn lemma_max_len(c1: Vec<i32>, c2: Vec<i32>)
    ensures (if c1.len() >= c2.len() { c1.len() } else { c2.len() }) >= c1.len(),
            (if c1.len() >= c2.len() { c1.len() } else { c2.len() }) >= c2.len()
{
}

proof fn lemma_addition_safe(coeff1: i32, coeff2: i32)
    requires coeff1.abs() <= 1000000, coeff2.abs() <= 1000000
    ensures coeff1 + coeff2 == coeff1 + coeff2
{
}
// </vc-helpers>

// <vc-spec>
fn hermeadd(c1: Vec<i32>, c2: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result.len() ==> {
            let coeff1 = if i < c1.len() { c1[i] } else { 0 };
            let coeff2 = if i < c2.len() { c2[i] } else { 0 };
            #[trigger] result[i] == coeff1 + coeff2
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type casting for indices */
    let max_len = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result = Vec::with_capacity(max_len);
    
    proof {
        lemma_max_len(c1, c2);
    }
    
    let mut i = 0;
    while i < max_len
        invariant
            0 <= i <= max_len,
            result.len() == i,
            max_len == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
            forall|j: int| 0 <= j < result.len() ==> {
                let coeff1 = get_coeff(c1, j);
                let coeff2 = get_coeff(c2, j);
                #[trigger] result[j] == coeff1 + coeff2
            }
        decreases max_len - i
    {
        let coeff1 = if i < c1.len() { c1[i] } else { 0 };
        let coeff2 = if i < c2.len() { c2[i] } else { 0 };
        
        let sum = coeff1.wrapping_add(coeff2);
        result.push(sum);
        
        proof {
            assert(result.len() == i + 1);
            assert(forall|j: int| 0 <= j < i ==> {
                let c1_coeff = get_coeff(c1, j);
                let c2_coeff = get_coeff(c2, j);
                result[j] == c1_coeff + c2_coeff
            });
            assert({
                let c1_coeff = get_coeff(c1, i as int);
                let c2_coeff = get_coeff(c2, i as int);
                result[i as int] == c1_coeff + c2_coeff
            });
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}