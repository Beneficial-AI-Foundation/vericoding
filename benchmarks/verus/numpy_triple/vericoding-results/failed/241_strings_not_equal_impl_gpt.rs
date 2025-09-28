// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compare Strings directly to satisfy ensures */
fn str_ne(a: &String, b: &String) -> (result: bool)
    ensures
        result == (*a != *b),
{
    let r = *a != *b;
    r
}

// </vc-helpers>

// <vc-spec>
fn not_equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] != x2[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate and compare using corrected helper */
    let n: usize = x1.len();
    let mut res: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            x1.len() == n,
            x2.len() == n,
            i <= n,
            res.len() == i,
            forall|j: int| 0 <= j < i as int ==> res[j] == (x1[j] != x2[j]),
        decreases (n as int) - (i as int)
    {
        let b: bool = str_ne(&x1[i], &x2[i]);
        res.push(b);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}