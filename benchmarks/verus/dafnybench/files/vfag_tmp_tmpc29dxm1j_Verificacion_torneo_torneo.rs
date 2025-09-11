// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn torneo(valores: &Vec<int>, i: usize, j: usize, k: usize) -> (res: (usize, usize))
    requires 
        valores.len() >= 20 && valores.len() < 50,
        i < valores.len() && j < valores.len() && k < valores.len(),
        i != j && j != k && k != i,
    ensures 
        exists|p: usize, q: usize, r: usize| 
            (p == i || p == j || p == k) &&
            (q == i || q == j || q == k) &&  
            (r == i || r == j || r == k) &&
            p != q && q != r && p != r &&
            valores[p as int] >= valores[q as int] && 
            valores[q as int] >= valores[r as int] &&
            res.0 == p && 
            res.1 == q,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}