// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn choose_val(xi: i32, first_xp: i32, last_xp: i32, first_fp: i32, last_fp: i32) -> (res: i32)
    ensures
        xi <= first_xp ==> res == first_fp,
        xi >= last_xp ==> res == last_fp,
{
    if xi <= first_xp {
        first_fp
    } else if xi >= last_xp {
        last_fp
    } else {
        first_fp
    }
}
// </vc-helpers>

// <vc-spec>
fn interp(x: Vec<i32>, xp: Vec<i32>, fp: Vec<i32>) -> (result: Vec<i32>)
    requires 
        xp.len() > 0,
        fp.len() == xp.len(),
        x.len() > 0,
        forall|i: int, j: int| 0 <= i < j < xp.len() ==> xp[i] < xp[j],
    ensures 
        result.len() == x.len(),
        forall|k: int| 0 <= k < x.len() ==> (
            (x[k] <= xp[0] ==> result[k] == fp[0]) &&
            (x[k] >= xp[xp.len() - 1] ==> result[k] == fp[fp.len() - 1])
        )
// </vc-spec>
// <vc-code>
{
    let n_xp = xp.len();
    let n_fp = fp.len();
    let n_x = x.len();

    let first_xp = xp[0];
    let last_index = n_xp - 1;
    let last_xp = xp[last_index];
    let first_fp = fp[0];
    proof {
        assert(n_fp == n_xp);
        assert(last_index < n_fp);
    }
    let last_fp = fp[last_index];

    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n_x
        invariant
            i <= n_x,
            res.len() == i,
            forall|k: int| 0 <= k < res.len() ==> (
                (x@[k] <= first_xp ==> res@[k] == first_fp) &&
                (x@[k] >= last_xp ==> res@[k] == last_fp)
            ),
        decreases n_x - i
    {
        let xi = x[i];
        let old_res_seq = res@;
        proof { assert(res@.len() == res.len() as int); }
        let old_len_int = res.len() as int;
        let v = choose_val(xi, first_xp, last_xp, first_fp, last_fp);
        res.push(v);
        proof {
            assert(res@ == old_res_seq.push(v));
            assert(res@.len() == old_res_seq.len() + 1);
            assert(forall|k: int| 0 <= k < old_res_seq.len() ==> res@[k] == old_res_seq[k]);
            assert(forall|k: int|
                0 <= k < old_res_seq.len() ==> (
                    (x@[k] <= first_xp ==> res@[k] == first_fp) &&
                    (x@[k] >= last_xp ==> res@[k] == last_fp)
                )
            );
            let k_new = old_res_seq.len();
            assert(k_new == old_len_int);
            assert(old_len_int == i as int);
            assert(k_new < res@.len());
            assert(res@[k_new] == v);
            assert(xi == x@[i as int]);
            if x@[k_new] <= first_xp {
                assert(v == first_fp);
            }
            if x@[k_new] >= last_xp {
                assert(v == last_fp);
            }
        }
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}