// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): return max of two int values */
fn max_int(a: int, b: int) -> (result: int)
    ensures
        result == if a >= b { a } else { b },
{
    if a >= b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn polysub(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result.len() ==> {
            if i < c1.len() && i < c2.len() {
                result[i] as int == c1[i] as int - c2[i] as int
            } else if i < c1.len() && i >= c2.len() {
                result[i] == c1[i]
            } else if i >= c1.len() && i < c2.len() {
                result[i] as int == 0 - c2[i] as int
            } else {
                result[i] == 0
            }
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute coefficient-wise subtraction using sequence view and int indices */
    let n1: int = c1.view().len();
    let n2: int = c2.view().len();
    let n: int = max_int(n1, n2);
    let mut res: Vec<i8> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i,
            i <= n,
            res.len() == (i as usize),
        decreases n - i
    {
        if i < n1 && i < n2 {
            let tmp: int = (c1.view()@[i] as int) - (c2.view()@[i] as int);
            res.push(#[verifier::truncate] tmp as i8);
        } else if i < n1 && i >= n2 {
            res.push(c1.view()@[i]);
        } else if i >= n1 && i < n2 {
            let tmp: int = 0 - (c2.view()@[i] as int);
            res.push(#[verifier::truncate] tmp as i8);
        } else {
            res.push(0i8);
        }
        i = i + 1;
    }
    res
}
// </vc-code>


}
fn main() {}