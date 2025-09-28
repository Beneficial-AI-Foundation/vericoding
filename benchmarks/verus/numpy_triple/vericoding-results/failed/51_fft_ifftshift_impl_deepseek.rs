// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn lemma_div_nonzero(a: int, b: int)
    requires
        b != 0,
    ensures
        a % b == a - b * (a / b)
{
}

proof fn lemma_div_remainder_properties(a: int, b: int)
    requires
        b > 0,
    ensures
        0 <= a % b < b,
        a % b == a - b * (a / b)
{
}

proof fn lemma_mod_distributive_property(a: int, b: int, n: int)
    requires
        n > 0,
    ensures
        (a + b) % n == (a % n + b % n) % n
{
}

proof fn lemma_mod_nonnegative(a: int, n: int)
    requires
        n > 0,
    ensures
        0 <= a % n < n
{
}

/* helper modified by LLM (iteration 5): Fix type conversion issues in helpers */

// </vc-helpers>

// <vc-spec>
fn ifftshift(x: Vec<f32>) -> (result: Vec<f32>)
    requires x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < x@.len() ==> 
            result[i] == x[((i + (x@.len() as int) / 2) % (x@.len() as int)) as int]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix type conversions and remove invalid invariant call */
    let len: usize = x.len();
    let len_int: int = len as int;
    let mut result = Vec::<f32>::new();
    let mut i: usize = 0;
    
    while i < len
        invariant
            0 <= i <= len,
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result@[j] == x@[((j + (len_int/2)) % len_int) as usize]
        decreases len - i
    {
        let index: usize = (((i as int) + (len_int/2)) % len_int) as usize;
        result.push(x[index]);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}