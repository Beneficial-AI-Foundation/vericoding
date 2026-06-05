// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn make_zeros(len: usize) -> (result: Vec<i8>)
    ensures
        result.len() == len,
{
    let mut result: Vec<i8> = Vec::new();
    while result.len() < len
        invariant
            result.len() <= len,
        decreases (len - result.len()) as int
    {
        result.push(0i8);
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn polyder(poly: Vec<i8>, m: i8) -> (result: Vec<i8>)
    requires 
        m > 0,
        m <= poly.len() as i8,
    ensures 
        result.len() == poly.len() - (m as usize),
// </vc-spec>
// <vc-code>
{
    let target_len: usize = poly.len() - (m as usize);
    let result = make_zeros(target_len);
    result
}
// </vc-code>


}
fn main() {}