// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): establish basic shift-by-zero identity */
proof fn lemma_shr_zero(a: i32)
    ensures
        a >> 0 == a,
{
    assert(a >> 0 == a);
}

/* helper modified by LLM (iteration 5): division by one identity */
proof fn lemma_div_by_one(a: i32)
    ensures
        a / 1i32 == a,
{
    assert(a / 1i32 == a);
}

/* helper modified by LLM (iteration 5): for nonnegative values, right shift equals division by power of two */
proof fn lemma_shr_eq_div_pow2_nonneg(a: i32, b: i32)
    requires
        a >= 0,
        b >= 0,
    ensures
        (a >> b) == a / (1i32 << b),
{
    assert((a >> b) == a / (1i32 << b));
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
    /* code modified by LLM (iteration 5): avoid calling proof-mode lemmas in exec code; compute by cases */
    let n = x1.len();
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            res.len() == i,
            (i as int) <= (n as int),
            x1.len() == n,
            x2.len() == n,
            forall|j: int| 0 <= j < i as int ==> {
                &&& (x1[j] >= 0 ==> res[j] == x1[j] / (1i32 << x2[j]))
                &&& (x1[j] < 0 ==> res[j] == x1[j] >> x2[j])
                &&& (x2[j] == 0 ==> res[j] == x1[j])
                &&& (x1[j] > 0 ==> res[j] >= 0)
                &&& (x1[j] < 0 ==> res[j] <= 0)
                &&& (x1[j] == 0 ==> res[j] == 0)
            },
        decreases n as int - i as int
    {
        let a = x1[i];
        let b = x2[i];
        let v: i32;
        if b == 0 {
            v = a;
        } else if a >= 0 {
            v = a / (1i32 << b);
        } else {
            v = a >> b;
        }

        res.push(v);

        proof {
            if a >= 0 {
                if b == 0 {
                    lemma_div_by_one(a);
                    assert(v == a);
                    assert(v == a / (1i32 << b));
                } else {
                    assert(v == a / (1i32 << b));
                }
            } else {
                if b == 0 {
                    lemma_shr_zero(a);
                    assert(v == a);
                    assert(v == a >> b);
                } else {
                    assert(v == a >> b);
                }
            }
            if a > 0 {
                // v is either a (b==0) or a/(2^b) with positive divisor; both are >= 0
                assert(v >= 0);
            }
            if a < 0 {
                // Right shift of a negative or a itself when b==0 is nonpositive
                if b == 0 {
                    assert(v <= 0);
                } else {
                    assert(v <= 0);
                }
            }
            if a == 0 {
                if b == 0 {
                    assert(v == 0);
                } else {
                    assert(0 >> b == 0);
                    assert(v == 0);
                }
            }
        }

        i += 1;
    }
    res
}
// </vc-code>

}
fn main() {}