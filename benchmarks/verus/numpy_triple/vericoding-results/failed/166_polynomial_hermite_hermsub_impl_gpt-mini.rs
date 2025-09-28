// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): return max for usize */
fn max_usize(a: usize, b: usize) -> (result: usize)
    ensures
        result == if a >= b { a } else { b },
{
    let result = if a >= b { a } else { b };
    result
}
// </vc-helpers>

// <vc-spec>
fn hermsub(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < c1.len() && 0 <= i < c2.len() ==> 
            result@[i] == c1@[i] - c2@[i],
        c1.len() > c2.len() ==> forall|i: int| 
            c2.len() <= i < c1.len() ==> result@[i] == c1@[i],
        c2.len() > c1.len() ==> forall|i: int| 
            c1.len() <= i < c2.len() ==> result@[i] == -c2@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement hermsub using usize indices and helper max_usize */
    let n1: usize = c1.len();
    let n2: usize = c2.len();
    let res_len: usize = max_usize(n1, n2);
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < res_len
        invariant
            i <= res_len,
            result.len() == i,
            forall|k: int| 0 <= k < i as int ==> if k < n1 as int && k < n2 as int { result@[k] == c1@[k] - c2@[k] } else if k < n1 as int { result@[k] == c1@[k] } else { result@[k] == -c2@[k] },
        decreases
            res_len - i
    {
        if i < n1 && i < n2 {
            let a: i8 = c1[i];
            let b: i8 = c2[i];
            result.push(a - b);
        } else if i < n1 {
            let a: i8 = c1[i];
            result.push(a);
        } else {
            let b: i8 = c2[i];
            result.push(-b);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}