// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed requires/ensures from spec function */
spec fn can_multiply_without_overflow(a: i32, b: i32, c: i32) -> bool {
    let ab = a as int * b as int;
    let result = ab * c as int;
    result >= i32::MIN as int && result <= i32::MAX as int
}

spec fn safe_multiply(a: i32, b: i32, c: i32) -> int {
    a as int * b as int * c as int
}
// </vc-helpers>

// <vc-spec>
fn chebder(c: Vec<i32>, scl: i32) -> (result: Vec<i32>)
    requires c.len() > 0,
    ensures
        result.len() == c.len() - 1,
        c.len() > 1 ==> result[0] == scl * c[1],
        c.len() > 2 ==> result[1] == scl * 4 * c[2],
        forall|j: int| 2 <= j < result.len() ==>
            result[j] == scl * (2 * ((j + 1) as i32)) * c[j + 1],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): using spec function for multiplication */
    let mut der = Vec::new();
    
    if c.len() == 1 {
        return der;
    }
    
    der.push(scl * c[1]);
    
    if c.len() == 2 {
        return der;
    }
    
    der.push(scl * 4 * c[2]);
    
    let mut j = 2;
    while j < c.len() - 1
        invariant
            j >= 2,
            j <= c.len() - 1,
            der.len() == j,
            der.len() >= 1,
            der[0] == scl * c[1],
            c.len() > 2 ==> der.len() >= 2 && der[1] == scl * 4 * c[2],
            forall|k: int| 2 <= k < der.len() ==> der[k] == scl * (2 * ((k + 1) as i32)) * c[k + 1]
        decreases c.len() - 1 - j
    {
        der.push(scl * (2 * ((j + 1) as i32)) * c[j + 1]);
        j += 1;
    }
    
    der
}
// </vc-code>

}
fn main() {}