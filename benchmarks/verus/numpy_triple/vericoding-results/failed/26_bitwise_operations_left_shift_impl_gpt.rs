// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): step lemma for powers of two */
pub proof fn lemma_pow_two_succ(n: nat)
    ensures
        pow(2, n + 1) == pow(2, n) * 2,
{
    assert(pow(2, n + 1) == pow(2, n) * 2);
}

/* helper modified by LLM (iteration 5): base case for pow(2, 0) */
pub proof fn lemma_pow_two_base()
    ensures
        pow(2, 0) == 1,
{
    assert(pow(2, 0) == 1);
}

/* helper modified by LLM (iteration 5): casting nonnegative i32 to usize then nat preserves the numeric value */
pub proof fn lemma_nonneg_i32_usize_nat_eq(z: i32)
    requires
        z >= 0,
    ensures
        ((z as usize) as nat) == (z as nat),
{
    assert(((z as usize) as int) == (z as int));
    assert(((z as usize) as nat) == (z as nat));
}
// </vc-helpers>

// <vc-spec>
fn left_shift(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == x1[i] * pow(2, x2[i] as nat),
        forall|i: int| 0 <= i < result.len() && x2[i] == 0 ==> result[i] == x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] == 0 ==> result[i] == 0,
        forall|i: int| 0 <= i < result.len() && x1[i] > 0 && x2[i] > 0 ==> result[i] > x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] < 0 && x2[i] > 0 ==> result[i] < x1[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): remove exec 'int' usage; reason about indices as int only inside proof blocks */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j] == x1[j] * pow(2, x2[j] as nat),
        decreases x1.len() - i
    {
        let mut val: i32 = x1[i];
        let k: usize = x2[i] as usize;
        let mut t: usize = 0;

        proof { lemma_pow_two_base(); }
        proof {
            assert((val as int) == (x1[i as int] as int));
            assert(pow(2, 0) == 1);
        }

        while t < k
            invariant
                t <= k,
                (val as int) == (x1[i as int] as int) * pow(2, t as nat),
            decreases k - t
        {
            let prev_t: usize = t;
            let prev_val: i32 = val;
            proof { lemma_pow_two_succ(prev_t as nat); }
            val = prev_val * 2;
            t = prev_t + 1;
            proof {
                assert((val as int) == (prev_val as int) * 2);
                assert(pow(2, t as nat) == pow(2, (prev_t as nat) + 1));
                assert(pow(2, (prev_t as nat) + 1) == pow(2, prev_t as nat) * 2);
            }
        }

        proof {
            let i_int = i as int;
            assert(x1.len() == x2.len());
            assert(i < x1.len());
            assert(i < x2.len());
            assert(0 <= i_int && i_int < x2.len() as int);
            assert(x2[i_int] >= 0);
            lemma_nonneg_i32_usize_nat_eq(x2[i_int]);
            assert((k as nat) == (x2[i_int] as nat));
            assert(pow(2, k as nat) == pow(2, x2[i_int] as nat));
            assert((val as int) == (x1[i_int] as int) * pow(2, x2[i_int] as nat));
        }

        result.push(val);
        proof {
            let i_int = i as int;
            assert(0 <= i_int && i_int < result.len() as int);
            assert(result[i_int] == val);
            assert((result[i_int] as int) == (x1[i_int] as int) * pow(2, x2[i_int] as nat));
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}