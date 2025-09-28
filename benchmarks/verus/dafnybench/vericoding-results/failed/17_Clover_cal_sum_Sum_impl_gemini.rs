// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn sum_spec(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        n + sum_spec((n - 1) as nat)
    }
}

/* helper modified by LLM (iteration 3): added proof body to establish inductive step */
proof fn sum_is_formula(n: nat)
    ensures
        sum_spec(n) == n * (n + 1) / 2,
    decreases n
{
    if n > 0 {
        sum_is_formula((n - 1) as nat);
        assert(sum_spec(n) == n + sum_spec((n - 1) as nat));
    }
}

/* helper modified by LLM (iteration 3): added lemma for monotonicity of sum_spec for overflow checks */
proof fn sum_spec_monotonic(i: nat, j: nat)
    requires i <= j
    ensures sum_spec(i) <= sum_spec(j)
    decreases j - i
{
    if i < j {
        sum_spec_monotonic(i, j - 1);
        assert(sum_spec(j) == j + sum_spec(j-1));
    }
}
// </vc-helpers>

// <vc-spec>
fn sum(n: u32) -> (s: u32)
    requires n >= 0
    ensures s == n * (n + 1) / 2
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): corrected invariants and added proofs for correctness and overflow */
{
    proof {
        sum_is_formula(n as nat);
    }

    let mut s: u32 = 0;
    let mut i: u32 = 0;

    while i < n
        invariant
            i <= n,
            s as nat == sum_spec(i as nat),
            sum_spec(n as nat) == (n as nat * (n as nat + 1)) / 2,
        decreases n - i
    {
        proof {
            sum_spec_monotonic((i + 1) as nat, n as nat);
            assert(sum_spec((i + 1) as nat) == sum_spec(i as nat) + (i + 1) as nat);
        }
        
        i = i + 1;
        s = s + i;
    }
    
    s
}
// </vc-code>

}
fn main() {}