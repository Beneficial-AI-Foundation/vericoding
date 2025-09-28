// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed cast operation to use builtin conversion */
fn safe_mult_i8(a: i8, b: i8) -> (res: i8)
    requires
        -128 <= (a as int) * (b as int) <= 127,
    ensures
        res == a * b,
{
    a * b
}

fn safe_cast_to_i8(x: int) -> (res: i8)
    requires
        -128 <= x <= 127,
    ensures
        res as int == x,
{
    builtin::cast_i8(x)
}
// </vc-helpers>

// <vc-spec>
fn chebder(c: Vec<i8>, scl: i8) -> (result: Vec<i8>)
    requires c.len() > 0,
    ensures
        result.len() == c.len() - 1,
        c.len() > 1 ==> result[0] == scl * c[1],
        c.len() > 2 ==> result[1] == scl * 4 * c[2],
        forall|j: int| 2 <= j < result.len() ==>
            result[j as int] == scl * (2 * ((j + 1) as i8)) * c[(j + 1) as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed cast operations to use int arithmetic */
    let n = c.len();
    let mut result = Vec::new();
    
    if n == 1 {
        return result;
    }
    
    // For c.len() > 1, add first element
    result.push(scl * c[1]);
    
    if n == 2 {
        return result;
    }
    
    // For c.len() > 2, add second element
    result.push(scl * 4 * c[2]);
    
    // Add remaining elements
    let mut j = 2;
    while j < n - 1
        invariant
            result.len() == j,
            j >= 2,
            j < n,
            n == c.len(),
            n > 2,
            result[0] == scl * c[1],
            result[1] == scl * 4 * c[2],
            forall|k: int| 2 <= k < result.len() ==> result[k] == scl * (2 * (k + 1) as i8) * c[k + 1],
        decreases n - 1 - j
    {
        result.push(scl * (2 * (j + 1) as i8) * c[j + 1]);
        j += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}