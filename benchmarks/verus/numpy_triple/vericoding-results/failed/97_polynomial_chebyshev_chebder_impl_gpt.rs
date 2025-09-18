// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): correct coefficient typing and element computation helpers */
spec fn dcoef(i: int) -> i32 { 2i32 * ((i + 1) as i32) }
spec fn chebder_elem(c: Seq<i32>, scl: i32, i: int) -> i32
    requires 0 <= i < c.len() - 1
{ if i == 0 { scl * c[i + 1] } else if i == 1 { scl * 4i32 * c[i + 1] } else { scl * dcoef(i) * c[i + 1] } }
// </vc-helpers>

// <vc-spec>
fn chebder(c: Vec<i32>, scl: i32) -> (result: Vec<i32>)
    requires c.len() > 0,
    ensures
        result.len() == c.len() - 1,
        c.len() > 1 ==> result[0] == scl * c[1],
        c.len() > 2 ==> result[1] == scl * 4 * c[2],
        forall|j: int| 2 <= j < result.len() ==>
            result[j] == scl * (2 * ((j + 1) as i32)) * c[j + 1],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): build derivative vector with loop invariants and fix forall proof syntax */
    let n = c.len();
    let mut res: Vec<i32> = Vec::new();

    if n > 1 {
        res.push(scl * c[1]);
    }
    if n > 2 {
        res.push(scl * 4i32 * c[2]);
    }
    if n > 3 {
        let mut j: usize = 2;
        while j < n - 1
            invariant
                n == c.len(),
                2 <= j as int <= (n as int) - 1,
                res.len() == j as int,
                res.len() <= (n as int) - 1,
                forall|i: int| 2 <= i < res.len() ==> res@[i] == scl * (2i32 * ((i + 1) as i32)) * c@[i + 1]
            decreases ((n - 1 - j) as int)
        {
            let old_len: int = res.len();
            let old_view = res@;
            let val = scl * (2i32 * ((j + 1) as i32)) * c[j + 1];
            res.push(val);

            proof {
                assert(res@ == old_view.push(val));
                assert(old_len == j as int);
                assert_forall_by(|i: int| {
                    requires true;
                    ensures 2 <= i < res.len() ==> res@[i] == scl * (2i32 * ((i + 1) as i32)) * c@[i + 1];
                    {
                        if 2 <= i && i < res.len() {
                            if i < old_len {
                                assert(old_view.len() == old_len);
                                assert(res@[i] == old_view.push(val)@[i]);
                                assert(old_view@[i] == scl * (2i32 * ((i + 1) as i32)) * c@[i + 1]);
                            } else {
                                assert(i == old_len);
                                assert(res@[i] == old_view.push(val)@[old_len]);
                                assert(res@[i] == val);
                                assert(res@[i] == scl * (2i32 * ((i + 1) as i32)) * c@[i + 1]);
                            }
                        }
                    }
                });
            }

            j = j + 1;
        }
    }

    proof {
        // First two coefficients if they exist
        if n > 1 {
            assert(res.len() >= 1);
            assert(res[0] == scl * c[1]);
        }
        if n > 2 {
            assert(res.len() >= 2);
            assert(res[1] == scl * 4i32 * c[2]);
        }
        // General case j >= 2
        assert_forall_by(|j: int| {
            requires true;
            ensures 2 <= j < res.len() ==> res[j] == scl * (2i32 * ((j + 1) as i32)) * c[j + 1];
            {
                if 2 <= j && j < res.len() {
                    assert(res@[j] == scl * (2i32 * ((j + 1) as i32)) * c@[j + 1]);
                    assert(res[j] == res@[j]);
                    assert(c[j + 1] == c@[j + 1]);
                }
            }
        });
    }

    res
}
// </vc-code>

}
fn main() {}