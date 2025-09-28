// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn is_optimal_savings(n: int, savings: int) -> bool {
    n >= 1 ==> (
        savings >= 0 &&
        (2 + savings) * (savings + 1) / 2 > n + 1 &&
        (savings == 0 || (2 + (savings - 1)) * savings / 2 <= n + 1)
    )
}

spec fn is_minimal_savings(n: int, savings: int) -> bool {
    n >= 1 ==> (
        is_optimal_savings(n, savings) &&
        (forall|j: int| j >= 0 && j < savings ==> #[trigger] ((2 + j) * (j + 1) / 2) <= n + 1)
    )
}

spec fn optimal_cost(n: int, savings: int) -> int {
    if n >= 1 && is_optimal_savings(n, savings) {
        n - savings + 1
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): triangular number definition */
spec fn tri(n: int) -> int {
    (2 + n) * (n + 1) / 2
}

/* helper modified by LLM (iteration 5): tri monotonicity lemma */
fn tri_monotone(k: int)
    requires
        k >= 0,
    ensures
        tri(k + 1) > tri(k),
{
    proof {
        assert(tri(k + 1) == (2 + (k + 1)) * ((k + 1) + 1) / 2);
        assert(tri(k) == (2 + k) * (k + 1) / 2);
        assert(tri(k + 1) - tri(k) == k + 2);
        assert(k + 2 > 0);
        assert(tri(k + 1) > tri(k));
    }
}

/* helper modified by LLM (iteration 5): tri non-decreasing up to k */
fn tri_non_decreasing_up_to(k: int)
    requires
        k >= 0,
    ensures
        forall|m: int| m >= 0 && m <= k ==> tri(m) <= tri(k),
{
    proof {
        if k == 0 {
            assert(forall|m: int| m >= 0 && m <= 0 ==> tri(m) <= tri(0))
        } else {
            tri_non_decreasing_up_to(k - 1);
            assert(forall|m: int| m >= 0 && m <= k - 1 ==> tri(m) <= tri(k - 1));
            tri_monotone(k - 1);
            assert(tri(k - 1) < tri(k));
            assert(forall|m: int| m >= 0 && m <= k - 1 ==> tri(m) <= tri(k));
            assert(forall|m: int| m >= 0 && m <= k ==> tri(m) <= tri(k));
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires 
        valid_input(n as int)
    ensures 
        result as int >= 1,
        result as int <= n as int,
        exists|savings: int| is_minimal_savings(n as int, savings) && result as int == optimal_cost(n as int, savings),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute minimal savings using runtime integers and prove spec properties in proof block */
    let n_i32: i32 = n as i32;
    let mut j: i32 = 0;

    while ( (2 + j) * (j + 1) / 2 ) <= n_i32 + 1
        invariant
            j >= 0,
        decreases n_i32 + 2 - ((2 + j) * (j + 1) / 2)
    {
        j = j + 1;
    }

    let savings_i32 = j;
    let result_i32 = n_i32 - savings_i32 + 1;

    proof {
        let n_i: int = n as int;
        let savings: int = savings_i32 as int;
        let result_i: int = result_i32 as int;

        // basic bounds
        assert(savings >= 0);

        // tri(savings) matches runtime formula and is > n + 1 by loop exit
        assert(tri(savings) == (2 + savings) * (savings + 1) / 2);
        assert(tri(savings) > n_i + 1);

        // savings must be >= 1 (tri(0) = 1 <= n+1 for n>=1)
        assert(tri(0) == 1);
        assert(tri(0) <= n_i + 1);
        assert(savings >= 1);

        // let k = savings - 1; tri(k) <= n + 1 because loop condition held for k
        let k: int = savings - 1;
        assert(k >= 0);
        assert(tri(k) == (2 + k) * (k + 1) / 2);
        assert(tri(k) <= n_i + 1);

        // monotonicity: for all m <= k, tri(m) <= tri(k) <= n+1
        tri_non_decreasing_up_to(k);
        assert(forall|m: int| m >= 0 && m <= k ==> tri(m) <= tri(k));
        assert(forall|m: int| m >= 0 && m < savings ==> tri(m) <= n_i + 1);

        // is_optimal_savings: savings >= 0, tri(savings) > n+1, and predecessor <= n+1
        assert(is_optimal_savings(n_i, savings));

        // is_minimal_savings: optimal and all smaller j satisfy tri(j) <= n+1
        assert(is_minimal_savings(n_i, savings));

        // result bounds
        assert(result_i >= 1);
        assert(result_i <= n_i);

        // result matches optimal_cost
        assert(result_i == optimal_cost(n_i, savings));

        // conclude existential
        assert(exists|s: int| is_minimal_savings(n_i, s) && result_i == optimal_cost(n_i, s));
    }

    (result_i32 as i8)
}

// </vc-code>


}

fn main() {}