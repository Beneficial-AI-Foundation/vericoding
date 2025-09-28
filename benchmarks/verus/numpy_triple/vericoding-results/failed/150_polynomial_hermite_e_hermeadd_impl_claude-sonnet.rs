// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added overflow checking for safe addition */
fn get_coeff(coeffs: &Vec<i8>, i: usize) -> (result: i8)
    requires
        i < usize::MAX,
    ensures
        #[trigger] result as int == if i < coeffs@.len() { coeffs@[i as int] as int } else { 0 },
{
    if i < coeffs.len() {
        coeffs[i]
    } else {
        0
    }
}

fn safe_add_i8(a: i8, b: i8) -> (result: i8)
    requires
        -128 <= a as int + b as int <= 127,
    ensures
        result as int == a as int + b as int,
{
    a + b
}
// </vc-helpers>

// <vc-spec>
fn hermeadd(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result@.len() ==> {
            let coeff1 = if i < c1@.len() { c1@[i] as int } else { 0 };
            let coeff2 = if i < c2@.len() { c2@[i] as int } else { 0 };
            #[trigger] result@[i] as int == coeff1 + coeff2
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): moved int conversions to proof blocks */
    let len1 = c1.len();
    let len2 = c2.len();
    let result_len = if len1 >= len2 { len1 } else { len2 };
    
    let mut result = Vec::with_capacity(result_len);
    let mut i = 0;
    
    while i < result_len
        invariant
            result.len() == i,
            i <= result_len,
            result_len == if len1 >= len2 { len1 } else { len2 },
            forall|j: int| 0 <= j < i ==> {
                let coeff1 = if j < c1@.len() { c1@[j] as int } else { 0 };
                let coeff2 = if j < c2@.len() { c2@[j] as int } else { 0 };
                #[trigger] result@[j] as int == coeff1 + coeff2
            },
        decreases result_len - i
    {
        let coeff1 = get_coeff(&c1, i);
        let coeff2 = get_coeff(&c2, i);
        
        proof {
            let coeff1_int = coeff1 as int;
            let coeff2_int = coeff2 as int;
            let sum_int = coeff1_int + coeff2_int;
        }
        
        let sum = if coeff1 as i16 + coeff2 as i16 > 127 {
            127i8
        } else if coeff1 as i16 + coeff2 as i16 < -128 {
            -128i8
        } else {
            (coeff1 as i16 + coeff2 as i16) as i8
        };
        
        result.push(sum);
        
        proof {
            let j = i as int;
            let expected_coeff1 = if j < c1@.len() { c1@[j] as int } else { 0 };
            let expected_coeff2 = if j < c2@.len() { c2@[j] as int } else { 0 };
            let coeff1_int = coeff1 as int;
            let coeff2_int = coeff2 as int;
            let sum_int = coeff1_int + coeff2_int;
            assert(expected_coeff1 == coeff1_int);
            assert(expected_coeff2 == coeff2_int);
            assert(result@[j] as int == sum_int);
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}