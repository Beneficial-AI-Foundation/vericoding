// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): i8 difference helper ensures int-cast difference equality */
fn diff_i8(a: i8, b: i8) -> (d: i8)
    ensures
        d as int == b as int - a as int,
{
    b - a
}

// </vc-helpers>

// <vc-spec>
fn numpy_ediff1d(ary: Vec<i8>) -> (result: Vec<i8>)
    requires ary.len() > 0,
    ensures 
        result.len() == ary.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == ary[i + 1] as int - ary[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): remove unnecessary int casts in assertions; maintain invariants and build result */
    let n = ary.len();
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i + 1 < n
        invariant
            n == ary.len(),
            res.len() == i,
            i + 1 <= n,
            forall|k: int|
                0 <= k < res.len() as int ==> res@[k] as int == ary[k + 1] as int - ary[k] as int,
        decreases n - i
    {
        let old_len: usize = res.len();
        let ghost ov = res@;
        proof {
            assert_forall_by(|k: int| {
                if 0 <= k && k < old_len as int {
                    assert(ov[k] == res@[k]);
                    assert(res@[k] as int == ary[k + 1] as int - ary[k] as int);
                    assert(ov[k] as int == ary[k + 1] as int - ary[k] as int);
                }
            });
        }
        let d = diff_i8(ary[i], ary[i + 1]);
        res.push(d);
        proof {
            assert(old_len == i);
            assert(old_len + 1 < n);

            assert_forall_by(|k: int| {
                if 0 <= k && k < res.len() as int {
                    if k < old_len as int {
                        assert(res@[k] == ov[k]);
                        assert(ov[k] as int == ary[k + 1] as int - ary[k] as int);
                    } else {
                        assert(k == old_len as int);
                        assert(res@[old_len as int] == d);
                        assert(d as int == ary[old_len as int + 1] as int - ary[old_len as int] as int);
                    }
                }
            });
        }
        i += 1;
    }
    res
}
// </vc-code>


}
fn main() {}