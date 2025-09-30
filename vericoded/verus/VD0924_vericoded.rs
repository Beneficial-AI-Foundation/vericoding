use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
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
        let p0 = i;
        let q0 = j;
        let r0 = k;
        let res_ = (p0, q0);
        proof {
            assert(vi == valores[i as int]);
            assert(vj == valores[j as int]);
            assert(vk == valores[k as int]);
            assert(i != j);
            assert(j != k);
            assert(k != i);
            assert(valores[p0 as int] >= valores[q0 as int]);
            assert(valores[q0 as int] >= valores[r0 as int]);
            assert(exists|p: usize, q: usize, r: usize|
                (p == i || p == j || p == k) &&
                (q == i || q == j || q == k) &&
                (r == i || r == j || r == k) &&
                p != q && q != r && p != r &&
                valores[p as int] >= valores[q as int] &&
                valores[q as int] >= valores[r as int] &&
                res_.0 == p &&
                res_.1 == q
            );
        }
        res_
    } else if vi >= vk && vk >= vj {
        let p0 = i;
        let q0 = k;
        let r0 = j;
        let res_ = (p0, q0);
        proof {
            assert(vi == valores[i as int]);
            assert(vj == valores[j as int]);
            assert(vk == valores[k as int]);
            assert(i != j);
            assert(j != k);
            assert(k != i);
            assert(valores[p0 as int] >= valores[q0 as int]);
            assert(valores[q0 as int] >= valores[r0 as int]);
            assert(exists|p: usize, q: usize, r: usize|
                (p == i || p == j || p == k) &&
                (q == i || q == j || q == k) &&
                (r == i || r == j || r == k) &&
                p != q && q != r && p != r &&
                valores[p as int] >= valores[q as int] &&
                valores[q as int] >= valores[r as int] &&
                res_.0 == p &&
                res_.1 == q
            );
        }
        res_
    } else if vj >= vi && vi >= vk {
        let p0 = j;
        let q0 = i;
        let r0 = k;
        let res_ = (p0, q0);
        proof {
            assert(vi == valores[i as int]);
            assert(vj == valores[j as int]);
            assert(vk == valores[k as int]);
            assert(i != j);
            assert(j != k);
            assert(k != i);
            assert(valores[p0 as int] >= valores[q0 as int]);
            assert(valores[q0 as int] >= valores[r0 as int]);
            assert(exists|p: usize, q: usize, r: usize|
                (p == i || p == j || p == k) &&
                (q == i || q == j || q == k) &&
                (r == i || r == j || r == k) &&
                p != q && q != r && p != r &&
                valores[p as int] >= valores[q as int] &&
                valores[q as int] >= valores[r as int] &&
                res_.0 == p &&
                res_.1 == q
            );
        }
        res_
    } else if vj >= vk && vk >= vi {
        let p0 = j;
        let q0 = k;
        let r0 = i;
        let res_ = (p0, q0);
        proof {
            assert(vi == valores[i as int]);
            assert(vj == valores[j as int]);
            assert(vk == valores[k as int]);
            assert(i != j);
            assert(j != k);
            assert(k != i);
            assert(valores[p0 as int] >= valores[q0 as int]);
            assert(valores[q0 as int] >= valores[r0 as int]);
            assert(exists|p: usize, q: usize, r: usize|
                (p == i || p == j || p == k) &&
                (q == i || q == j || q == k) &&
                (r == i || r == j || r == k) &&
                p != q && q != r && p != r &&
                valores[p as int] >= valores[q as int] &&
                valores[q as int] >= valores[r as int] &&
                res_.0 == p &&
                res_.1 == q
            );
        }
        res_
    } else if vk >= vi && vi >= vj {
        let p0 = k;
        let q0 = i;
        let r0 = j;
        let res_ = (p0, q0);
        proof {
            assert(vi == valores[i as int]);
            assert(vj == valores[j as int]);
            assert(vk == valores[k as int]);
            assert(i != j);
            assert(j != k);
            assert(k != i);
            assert(valores[p0 as int] >= valores[q0 as int]);
            assert(valores[q0 as int] >= valores[r0 as int]);
            assert(exists|p: usize, q: usize, r: usize|
                (p == i || p == j || p == k) &&
                (q == i || q == j || q == k) &&
                (r == i || r == j || r == k) &&
                p != q && q != r && p != r &&
                valores[p as int] >= valores[q as int] &&
                valores[q as int] >= valores[r as int] &&
                res_.0 == p &&
                res_.1 == q
            );
        }
        res_
    } else {
        let p0 = k;
        let q0 = j;
        let r0 = i;
        let res_ = (p0, q0);
        proof {
            assert(vi == valores[i as int]);
            assert(vj == valores[j as int]);
            assert(vk == valores[k as int]);
            assert(i != j);
            assert(j != k);
            assert(k != i);
            assert(valores[p0 as int] >= valores[q0 as int]);
            assert(valores[q0 as int] >= valores[r0 as int]);
            assert(exists|p: usize, q: usize, r: usize|
                (p == i || p == j || p == k) &&
                (q == i || q == j || q == k) &&
                (r == i || r == j || r == k) &&
                p != q && q != r && p != r &&
                valores[p as int] >= valores[q as int] &&
                valores[q as int] >= valores[r as int] &&
                res_.0 == p &&
                res_.1 == q
            );
        }
        res_
    }
}
// </vc-code>

fn main() {}

}