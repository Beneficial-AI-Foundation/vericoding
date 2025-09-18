// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): arithmetic lemma for divisibility (n % k == 0) implies k * (n / k) == n */
proof fn mul_div_identity(n: nat, k: nat)
    requires
        k > 0,
        n % k == 0,
    ensures
        k * (n / k) == n
{
    assert(n == (n / k) * k + n % k);
    assert(n == (n / k) * k);
    assert(k * (n / k) == (n / k) * k);
    assert(k * (n / k) == n);
}

/* helper modified by LLM (iteration 5): bound idx within array using chunk size */
proof fn bound_idx(ii: nat, j: nat, n: nat, k: nat)
    requires
        k > 0,
        n % k == 0,
        ii < k,
        j < n / k,
    ensures
        ii * (n / k) + j < n
{
    mul_div_identity(n, k);
    let cs = n / k;
    assert(ii * cs + j < ii * cs + cs);
    assert(ii * cs + cs == (ii + 1) * cs);
    assert(ii + 1 <= k);
    assert((ii + 1) * cs <= k * cs);
    assert(k * cs == n);
    assert(ii * cs + j < n);
}
// </vc-helpers>

// <vc-spec>
fn split(arr: Vec<f32>, k: usize) -> (result: Vec<Vec<f32>>)
    requires
        k > 0,
        arr.len() % k == 0,
    ensures
        result.len() == k,
        forall|i: int| #[trigger] result[i].len() == (arr.len() / k) ==> (0 <= i < k),
        forall|i: int, j: int| 
            0 <= i < k && 0 <= j < (arr.len() / k) as int ==> {
                let idx = i * (arr.len() / k) as int + j;
                0 <= idx < arr.len() as int && #[trigger] result[i][j] == arr[idx]
            },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed forall to be pure expressions and tightened invariants; no internal assertions inside quantifier bodies */
    let n = arr.len();
    let cs = n / k;
    let mut res: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < k
        invariant
            k > 0,
            n == arr.len(),
            n % k == 0,
            cs == n / k,
            res.len() == i,
            i <= k,
            forall|ii: int, j: int|
                0 <= ii < i as int && 0 <= j < cs as int ==>
                    #[trigger] res@[ii][j] == arr@[ii * cs as int + j]
        decreases k - i
    {
        let lo: usize = i * cs;
        let hi: usize = lo + cs;
        proof {
            assert(i < k);
            let ii: nat = i as nat;
            let kn: nat = k as nat;
            let csn: nat = cs as nat;
            let nn: nat = n as nat;
            mul_div_identity(nn, kn);
            assert(csn == nn / kn);
            assert(ii + 1 <= kn);
            assert((ii + 1) * csn <= kn * csn);
            assert(kn * csn == nn);
            assert(hi <= n);
        }
        let mut chunk: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < cs
            invariant
                chunk.len() == j,
                j <= cs,
                forall|jj: int|
                    0 <= jj < j as int ==> #[trigger] chunk@[jj] == arr@[lo as int + jj]
            decreases cs - j
        {
            proof {
                assert(j < cs);
                assert(lo + j < lo + cs);
                assert(lo + cs == hi);
                assert(hi <= n);
                assert(lo + j < n);
            }
            chunk.push(arr[lo + j]);
            j = j + 1;
        }
        let old_len = res.len();
        res.push(chunk);
        proof {
            assert(old_len == i);
            assert(j == cs);
            assert(res@[i as int] == res@[old_len as int]);
            assert(res@[i as int] == chunk);
            assert(i as int * cs as int == lo as int);
            assert(forall|jj: int| 0 <= jj < cs as int ==> res@[i as int][jj] == chunk@[jj]);
            assert(forall|jj: int| 0 <= jj < cs as int ==> chunk@[jj] == arr@[lo as int + jj]);
            assert(forall|jj: int| 0 <= jj < cs as int ==> lo as int + jj == i as int * cs as int + jj);
            assert(forall|jj: int|
                0 <= jj < cs as int ==>
                    #[trigger] res@[i as int][jj] == arr@[i as int * cs as int + jj]
            );
        }
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}