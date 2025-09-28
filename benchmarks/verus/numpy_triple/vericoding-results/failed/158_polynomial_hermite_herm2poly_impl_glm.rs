// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): changed nat to int for non-ghost code */
fn hermite_coefficient(n: int, k: int) -> int
    requires n >= k,
{
    if k == 0 {
        if n % 2 == 0 { 1 } else { 0 }
    } else if n == k {
        1
    } else {
        2 * hermite_coefficient(n - 1, k - 1) + hermite_coefficient(n - 2, k)
    }
}
// </vc-helpers>

// <vc-spec>
fn herm2poly(c: Vec<i8>) -> (result: Vec<i8>)
    requires c.len() > 0,
    ensures
        result.len() == c.len(),
        /* Sanity checks */
        c.len() == 1 ==> result@ == c@,
        c.len() == 2 ==> result[0] == c[0] && result[1] as int == 2 * c[1] as int,
        /* Example from documentation: herm2poly([1, 2.75, 0.5, 0.375]) approximated with integers */
        (c.len() == 4 && c[0] as int == 1 && c[1] as int == 3 && c[2] as int == 1 && c[3] as int == 0) ==>
            (result[0] as int == 0 && result[1] as int == 1 && result[2] as int == 2 && result[3] as int == 3)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): changed nat to int for non-ghost code */
{
    let n = c.len() as int;
    let mut result = Vec::with_capacity(n as usize);
    
    for i in 0..n
        invariant
            result.len() == i as usize,
            forall|j: int| 0 <= j < i ==> result[j as usize] as int == hermite_coefficient(n - 1, j),
        decreases n - i
    {
        let coeff = hermite_coefficient(n - 1, i);
        result.push(coeff as i8);
    }
    
    result
}
// </vc-code>


}
fn main() {}