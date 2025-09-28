use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation.
// </vc-helpers>
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
            res.1 == q, // Q
// </vc-spec>
// <vc-code>
{
    let vi = valores[i];
    let vj = valores[j];
    let vk = valores[k];

    let mut p = i;
    let mut q = j;
    let mut r = k;

    if vi < vj {
        p = j;
        q = i;
    } else {
        p = i;
        q = j;
    }
    r = k;

    if valores[p] < valores[r] {
        let temp = p;
        p = r;
        r = temp;
    }

    if valores[q] < valores[r] {
        let temp = q;
        q = r;
        r = temp;
    }

    assert(p != q && q != r && p != r);
    assert(p == i || p == j || p == k);
    assert(q == i || q == j || q == k);
    assert(r == i || r == j || r == k);
    assert(valores[p as int] >= valores[q as int]);
    assert(valores[q as int] >= valores[r as int]);

    (p, q)
}
// </vc-code>

fn main() {}

}