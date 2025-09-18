// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): arithmetic right shift preserves sign for i32 */
proof fn lemma_shr_preserves_sign(x: i32, s: i32)
    requires
        s >= 0,
    ensures
        (x >= 0 ==> x >> s >= 0) &&
        (x < 0 ==> x >> s <= 0)
{
}

// </vc-helpers>

// <vc-spec>
fn right_shift(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            &&& (x1[i] >= 0 ==> result[i] == x1[i] / (1i32 << x2[i]))
            &&& (x1[i] < 0 ==> result[i] == x1[i] >> x2[i])
            &&& (x2[i] == 0 ==> result[i] == x1[i])
            &&& (x1[i] > 0 ==> result[i] >= 0)
            &&& (x1[i] < 0 ==> result[i] <= 0)
            &&& (x1[i] == 0 ==> result[i] == 0)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fix while-loop invariant syntax and types */
    let n: usize = x1.len();
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int && i as int <= n as int &&
            x1.len() == n && x2.len() == n &&
            res.len() == i &&
            forall|j: int| 0 <= j < i as int ==> {
                &&& (x1@[j] >= 0 ==> res@[j] == x1@[j] / (1i32 << x2@[j]))
                &&& (x1@[j] < 0 ==> res@[j] == x1@[j] >> x2@[j])
                &&& (x2@[j] == 0 ==> res@[j] == x1@[j])
                &&& (x1@[j] > 0 ==> res@[j] >= 0)
                &&& (x1@[j] < 0 ==> res@[j] <= 0)
                &&& (x1@[j] == 0 ==> res@[j] == 0)
            }
        decreases n as int - i as int
    {
        let a = x1[i];
        let s = x2[i];
        let r = if s == 0 {
            a
        } else if a >= 0 {
            a / (1i32 << s)
        } else {
            a >> s
        };
        res.push(r);
        proof {
            let ii: int = i as int;
            assert(0 <= ii && ii < x1.len() as int);
            assert(0 <= ii && ii < x2.len() as int);
            assert(forall|k: int| 0 <= k < x2.len() as int ==> x2@[k] >= 0);
            assert(x1@[ii] == a);
            assert(x2@[ii] == s);
            assert(res@[ii] == r);
            if s == 0 {
                assert(res@[ii] == x1@[ii]);
            }
            if a >= 0 {
                assert(res@[ii] == x1@[ii] / (1i32 << x2@[ii]));
                assert(res@[ii] >= 0);
            }
            if a == 0 {
                assert(res@[ii] == 0);
            }
            if a < 0 {
                assert(res@[ii] == a >> s);
                lemma_shr_preserves_sign(a, s);
                assert(res@[ii] <= 0);
            }
        }
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}