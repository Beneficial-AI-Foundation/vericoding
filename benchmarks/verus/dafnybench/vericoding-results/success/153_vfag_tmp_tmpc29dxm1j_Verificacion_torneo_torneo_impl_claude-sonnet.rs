use vstd::prelude::*;

verus! {

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
            res.1 == q, // Q
// </vc-spec>
// <vc-code>
{
    let vi = valores[i];
    let vj = valores[j];
    let vk = valores[k];
    
    if vi >= vj && vj >= vk {
        // i >= j >= k
        proof {
            assert(exists|p: usize, q: usize, r: usize| 
                (p == i || p == j || p == k) &&
                (q == i || q == j || q == k) &&  
                (r == i || r == j || r == k) &&
                p != q && q != r && p != r &&
                valores[p as int] >= valores[q as int] && 
                valores[q as int] >= valores[r as int] &&
                i == p && 
                j == q) by {
                assert((i == i || i == j || i == k));
                assert((j == i || j == j || j == k));
                assert((k == i || k == j || k == k));
                assert(i != j && j != k && i != k);
                assert(valores[i as int] >= valores[j as int]);
                assert(valores[j as int] >= valores[k as int]);
            }
        }
        (i, j)
    } else if vi >= vk && vk >= vj {
        // i >= k >= j
        proof {
            assert(exists|p: usize, q: usize, r: usize| 
                (p == i || p == j || p == k) &&
                (q == i || q == j || q == k) &&  
                (r == i || r == j || r == k) &&
                p != q && q != r && p != r &&
                valores[p as int] >= valores[q as int] && 
                valores[q as int] >= valores[r as int] &&
                i == p && 
                k == q) by {
                assert((i == i || i == j || i == k));
                assert((k == i || k == j || k == k));
                assert((j == i || j == j || j == k));
                assert(i != k && k != j && i != j);
                assert(valores[i as int] >= valores[k as int]);
                assert(valores[k as int] >= valores[j as int]);
            }
        }
        (i, k)
    } else if vj >= vi && vi >= vk {
        // j >= i >= k
        proof {
            assert(exists|p: usize, q: usize, r: usize| 
                (p == i || p == j || p == k) &&
                (q == i || q == j || q == k) &&  
                (r == i || r == j || r == k) &&
                p != q && q != r && p != r &&
                valores[p as int] >= valores[q as int] && 
                valores[q as int] >= valores[r as int] &&
                j == p && 
                i == q) by {
                assert((j == i || j == j || j == k));
                assert((i == i || i == j || i == k));
                assert((k == i || k == j || k == k));
                assert(j != i && i != k && j != k);
                assert(valores[j as int] >= valores[i as int]);
                assert(valores[i as int] >= valores[k as int]);
            }
        }
        (j, i)
    } else if vj >= vk && vk >= vi {
        // j >= k >= i
        proof {
            assert(exists|p: usize, q: usize, r: usize| 
                (p == i || p == j || p == k) &&
                (q == i || q == j || q == k) &&  
                (r == i || r == j || r == k) &&
                p != q && q != r && p != r &&
                valores[p as int] >= valores[q as int] && 
                valores[q as int] >= valores[r as int] &&
                j == p && 
                k == q) by {
                assert((j == i || j == j || j == k));
                assert((k == i || k == j || k == k));
                assert((i == i || i == j || i == k));
                assert(j != k && k != i && j != i);
                assert(valores[j as int] >= valores[k as int]);
                assert(valores[k as int] >= valores[i as int]);
            }
        }
        (j, k)
    } else if vk >= vi && vi >= vj {
        // k >= i >= j
        proof {
            assert(exists|p: usize, q: usize, r: usize| 
                (p == i || p == j || p == k) &&
                (q == i || q == j || q == k) &&  
                (r == i || r == j || r == k) &&
                p != q && q != r && p != r &&
                valores[p as int] >= valores[q as int] && 
                valores[q as int] >= valores[r as int] &&
                k == p && 
                i == q) by {
                assert((k == i || k == j || k == k));
                assert((i == i || i == j || i == k));
                assert((j == i || j == j || j == k));
                assert(k != i && i != j && k != j);
                assert(valores[k as int] >= valores[i as int]);
                assert(valores[i as int] >= valores[j as int]);
            }
        }
        (k, i)
    } else {
        // k >= j >= i
        proof {
            assert(exists|p: usize, q: usize, r: usize| 
                (p == i || p == j || p == k) &&
                (q == i || q == j || q == k) &&  
                (r == i || r == j || r == k) &&
                p != q && q != r && p != r &&
                valores[p as int] >= valores[q as int] && 
                valores[q as int] >= valores[r as int] &&
                k == p && 
                j == q) by {
                assert((k == i || k == j || k == k));
                assert((j == i || j == j || j == k));
                assert((i == i || i == j || i == k));
                assert(k != j && j != i && k != i);
                assert(valores[k as int] >= valores[j as int]);
                assert(valores[j as int] >= valores[i as int]);
            }
        }
        (k, j)
    }
}
// </vc-code>

fn main() {}

}