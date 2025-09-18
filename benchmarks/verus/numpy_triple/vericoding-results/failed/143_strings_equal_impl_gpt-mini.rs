// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compare two Strings for equality */
fn str_eq(a: String, b: String) -> bool { a == b }
// </vc-helpers>

// <vc-spec>
fn equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] == x2[i]),
        forall|i: int| 0 <= i < result.len() ==> (result[i] == true <==> x1[i] == x2[i]),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i] == true,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate using int indices and maintain invariant relating res and inputs */
    let n: int = x1.len() as int;
    let mut res: Vec<bool> = Vec::new();
    res.reserve(x1.len());
    let mut i: int = 0;
    while i < n
        invariant res.len() == i as usize && forall|j: int| 0 <= j < i ==> res[j] == (x1[j as usize] == x2[j as usize])
        decreases n - i
    {
        let idx: usize = i as usize;
        let b: bool = x1[idx] == x2[idx];
        res.push(b);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}