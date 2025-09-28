// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): pointwise predicate capturing the allclose relation */
spec fn is_allclose_at(a: Seq<i8>, b: Seq<i8>, rtol: i8, atol: i8, i: int) -> bool {
    int_abs((a[i] - b[i]) as int) <= (atol as int + rtol as int * int_abs(b[i] as int))
}

/* helper modified by LLM (iteration 4): basic lemma unfolding int_abs on ints */
proof fn lemma_int_abs_unfold(x: int)
    ensures
        int_abs(x) == (if x >= 0 { x } else { -x }),
{
}

// </vc-helpers>

// <vc-spec>
fn allclose(a: Vec<i8>, b: Vec<i8>, rtol: i8, atol: i8) -> (result: bool)
    requires 
        a.len() == b.len(),
        rtol >= 0,
        atol >= 0,
    ensures 
        result == (forall|i: int| 0 <= i < a@.len() ==> 
            int_abs((a[i] - b[i]) as int) <= (atol as int + rtol as int * int_abs(b[i] as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): implement loop using widened i32 ops; avoid machine-int arithmetic inside proofs and bridge to spec via casts and case splits */
    let n: usize = a.len();
    let mut i: usize = 0usize;
    let mut ok: bool = true;

    while i < n
        invariant
            a.len() == n,
            b.len() == n,
            i <= n,
            ok == (forall|j: int| 0 <= j < i as int ==> is_allclose_at(a@, b@, rtol, atol, j)),
        decreases n - i
    {
        let ai: i8 = a[i];
        let bi: i8 = b[i];

        let ai32: i32 = ai as i32;
        let bi32: i32 = bi as i32;

        proof {
            assert(-128 <= ai32 && ai32 <= 127);
            assert(-128 <= bi32 && bi32 <= 127);
            assert(0 <= (rtol as i32) && (rtol as i32) <= 127);
            assert(0 <= (atol as i32) && (atol as i32) <= 127);
        }

        let diff32: i32 = ai32 - bi32;
        let absdiff32: i32 = if diff32 < 0 { -diff32 } else { diff32 };
        let bi_abs32: i32 = if bi32 < 0 { -bi32 } else { bi32 };

        proof {
            assert(-255 <= diff32 && diff32 <= 255);
            assert(0 <= absdiff32 && absdiff32 <= 255);
            if bi32 == -128 {
                assert(bi_abs32 == 128);
            } else {
                if bi32 < 0 {
                    assert(0 < bi_abs32 && bi_abs32 <= 127);
                } else {
                    assert(0 <= bi_abs32 && bi_abs32 <= 127);
                }
                assert(bi_abs32 <= 128);
            }
        }

        let rhs32: i32 = (atol as i32) + (rtol as i32) * bi_abs32;

        proof {
            assert(0 <= (rtol as i32) * bi_abs32);
            assert((rtol as i32) * bi_abs32 <= 127 * 128);
            assert(0 <= rhs32);
            assert(rhs32 <= 127 + 127 * 128);
        }

        let cond_exec: bool = absdiff32 <= rhs32;

        proof {
            let j: int = i as int;
            assert(0 <= j && j < a@.len());
            assert(a@[j] == ai);
            assert(b@[j] == bi);

            let ai_int: int = a@[j] as int;
            let bi_int: int = b@[j] as int;
            let diff_int: int = ai_int - bi_int;

            // Bridge absdiff32 to int_abs(diff_int)
            assert((diff32 as int) == diff_int);
            if diff32 < 0 {
                assert((absdiff32 as int) == (-(diff32 as int)));
                assert(int_abs(diff_int) == -diff_int);
                assert((absdiff32 as int) == int_abs(diff_int));
            } else {
                assert((absdiff32 as int) == (diff32 as int));
                assert(int_abs(diff_int) == diff_int);
                assert((absdiff32 as int) == int_abs(diff_int));
            }

            // Bridge bi_abs32 to int_abs(bi_int)
            if bi32 < 0 {
                assert((bi_abs32 as int) == (-(bi32 as int)));
                assert((bi32 as int) == bi_int);
                assert(int_abs(bi_int) == -bi_int);
                assert((bi_abs32 as int) == int_abs(bi_int));
            } else {
                assert((bi_abs32 as int) == (bi32 as int));
                assert((bi32 as int) == bi_int);
                assert(int_abs(bi_int) == bi_int);
                assert((bi_abs32 as int) == int_abs(bi_int));
            }

            // Bridge rhs32 to spec RHS
            assert(((atol as i32) as int) == (atol as int));
            assert(((rtol as i32) as int) == (rtol as int));
            assert(((rtol as i32) * bi_abs32 as int) == ((rtol as i32) as int) * (bi_abs32 as int));
            assert((rhs32 as int) == (atol as int) + (rtol as int) * (bi_abs32 as int));
            assert((rhs32 as int) == (atol as int) + (rtol as int) * int_abs(bi_int));

            // Order-preserving cast
            assert((absdiff32 <= rhs32) == ((absdiff32 as int) <= (rhs32 as int)));

            // Conclude pointwise equivalence
            assert(cond_exec == is_allclose_at(a@, b@, rtol, atol, j));
        }

        ok = ok && cond_exec;
        i += 1;
    }

    ok
}
// </vc-code>

}
fn main() {}