// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_spec(x: i32) -> nat {
    if x >= 0 { x as nat } else { (-x) as nat }
}

spec fn popcount(n: nat) -> nat 
    decreases n
{
    if n == 0 {
        0
    } else {
        (n % 2) + popcount(n / 2)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): strengthened lemmas for abs equivalence and popcount unfolding */
proof fn lemma_abs_spec_equiv(x: i32)
    ensures
        abs_spec(x) == if x >= 0 { x as nat } else { (-x) as nat },
{
    if x >= 0 {
        assert(abs_spec(x) == x as nat);
    } else {
        assert(abs_spec(x) == (-x) as nat);
    }
}

/* helper modified by LLM (iteration 5): unfold lemma for popcount recursion */
proof fn lemma_popcount_unfold(n: nat)
    ensures
        popcount(n) == if n == 0 { 0 } else { (n % 2) + popcount(n / 2) },
{
    if n == 0 {
        assert(popcount(n) == 0);
    } else {
        assert(popcount(n) == (n % 2) + popcount(n / 2));
    }
}

// </vc-helpers>

// <vc-spec>
fn bitwise_count(x: Vec<i32>) -> (result: Vec<nat>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == popcount(abs_spec(x[i])),
        forall|i: int| 0 <= i < result.len() ==> x[i] == 0 ==> result[i] == 0,
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute popcount via exec u64 with ghost reasoning linking to specs */
    let mut result: Vec<nat> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i as int ==> result[k] == popcount(abs_spec(x[k])),
        decreases x.len() - i
    {
        let xi = x[i];

        let mut m_u: u64 = if xi >= 0 { xi as u64 } else { (-(xi as i64)) as u64 };
        let ghost orig: nat = abs_spec(xi);
        proof {
            lemma_abs_spec_equiv(xi);
            assert(orig == if xi >= 0 { xi as nat } else { (-xi) as nat });
        }

        let mut pc_u: u64 = 0;
        let ghost mut mg: nat = orig;
        let ghost mut pcg: nat = 0;

        while m_u > 0
            invariant
                mg == m_u as nat,
                pcg == pc_u as nat,
                pcg + popcount(mg) == popcount(orig),
            decreases m_u as nat
        {
            let m_before: u64 = m_u;
            let pc_before: u64 = pc_u;
            let bit_u: u64 = m_before % 2;
            pc_u = pc_before + bit_u;
            m_u = m_before / 2;

            proof {
                let mg_old = mg;
                let pcg_old = pcg;
                assert(mg_old == m_before as nat);
                lemma_popcount_unfold(mg_old);
                mg = mg_old / 2;
                pcg = pcg_old + (mg_old % 2);

                // Relate exec updates to ghost updates
                assert((m_before as nat) % 2 == (m_before % 2) as nat);
                assert((m_before as nat) / 2 == (m_before / 2) as nat);
                assert(mg == m_u as nat);
                assert((pc_before as nat) + ((bit_u) as nat) == (pc_u) as nat);
                assert(pcg_old == pc_before as nat);
                assert(pcg == pc_u as nat);

                // Maintain main invariant
                assert(pcg_old + popcount(mg_old) == popcount(orig));
                assert(popcount(mg_old) == (mg_old % 2) + popcount(mg_old / 2));
                assert(pcg + popcount(mg) == pcg_old + (mg_old % 2) + popcount(mg_old / 2));
                assert(pcg + popcount(mg) == pcg_old + popcount(mg_old));
                assert(pcg + popcount(mg) == popcount(orig));
            }
        }

        proof {
            assert(m_u == 0);
            assert(mg == m_u as nat);
            assert(mg == 0);
            lemma_popcount_unfold(mg);
            assert(popcount(mg) == 0);
            assert(pcg + popcount(mg) == pcg);
            assert(pcg == popcount(orig));
            assert(pcg == pc_u as nat);
        }

        result.push(pc_u as nat);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}