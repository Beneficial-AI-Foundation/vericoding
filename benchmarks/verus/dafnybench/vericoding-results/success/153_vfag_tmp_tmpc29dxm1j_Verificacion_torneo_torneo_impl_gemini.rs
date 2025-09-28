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
    let vi = valores[i];
    let vj = valores[j];
    let vk = valores[k];

    if vi >= vj {
        if vj >= vk {
            // vi >= vj >= vk. p=i, q=j, r=k
            (i, j)
        } else { // vk > vj
            if vi >= vk {
                // vi >= vk > vj. p=i, q=k, r=j
                (i, k)
            } else { // vk > vi
                // vk > vi >= vj. p=k, q=i, r=j
                (k, i)
            }
        }
    } else { // vj > vi
        if vi >= vk {
            // vj > vi >= vk. p=j, q=i, r=k
            (j, i)
        } else { // vk > vi
            if vj >= vk {
                // vj >= vk > vi. p=j, q=k, r=i
                (j, k)
            } else { // vk > vj
                // vk > vj > vi. p=k, q=j, r=i
                (k, j)
            }
        }
    }
}
// </vc-code>

}
fn main() {}