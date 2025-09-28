use vstd::prelude::*;

verus! {

spec fn C(n: nat) -> nat
    decreases n
{
    if n == 0 { 
        1nat 
    } else { 
        ((4 * (n as int) - 2) * (C((n - 1) as nat) as int) / ((n as int) + 1)) as nat
    }
}

// <vc-helpers>
proof fn lemma_C_is_positive(n: nat)
    decreases n
{
    if n == 0 {
    } else {
        lemma_C_is_positive((n - 1) as nat);
        let C_n_minus_1 = C((n - 1) as nat);
        assert(C_n_minus_1 > 0);
        assert(((4 * (n as int) - 2) * (C_n_minus_1 as int)) >= 0);
        assert((n as int) + 1 > 0);
        assert((((4 * (n as int) - 2) * (C_n_minus_1 as int)) / ((n as int) + 1)) >= 0);
    }
}

proof fn lemma_C_is_non_decreasing(n: nat)
    decreases n
{
    if n == 0 {
    } else if n == 1 {
        lemma_C_is_positive(0);
        assert(C(1) >= C(0));
    } else {
        lemma_C_is_non_decreasing((n - 1) as nat);
        lemma_C_is_positive((n - 1) as nat);
        let C_n_minus_1 = C((n - 1) as nat);
        let C_n_minus_2 = C(((n - 1) as nat - 1) as nat);
        let four_n_minus_2 = 4 * (n as int) - 2;
        let n_plus_1 = (n as int) + 1;
        let four_n_minus_6 = 4 * ((n - 1) as int) - 2;
        let n_int = n as int;

        assert(C_n_minus_1 >= C_n_minus_2);
        assert(four_n_minus_2 >= 0 && n_plus_1 > 0 && four_n_minus_6 >= 0);
        assert((four_n_minus_2 * (C_n_minus_1 as int)) >= (four_n_minus_6 * (C_n_minus_2 as int)));
        assert(C(n) == ((four_n_minus_2 * (C_n_minus_1 as int)) / n_plus_1) as nat);
        assert(C((n - 1) as nat) == ((four_n_minus_6 * (C_n_minus_2 as int)) / n_int) as nat);
        assert(C(n) >= C((n - 1) as nat));
    }
}

spec fn div_is_exact(n: int, d: int) -> bool {
    n % d == 0
}

proof fn lemma_C_divisibility(k: nat)
    decreases k
{
    if k == 0 {
    } else {
        lemma_C_divisibility((k - 1) as nat);
        let four_k_minus_2 = 4 * (k as int) - 2;
        let k_plus_1 = (k as int) + 1;
        let C_k_minus_1_int = C((k - 1) as nat) as int;
        
        lemma_C_is_positive((k-1) as nat);
        assert(div_is_exact(four_k_minus_2 * C_k_minus_1_int, k_plus_1));
    }
}
// </vc-helpers>

// <vc-spec>
fn calcC(n: u64) -> (res: u64)
    ensures res == C(n as nat),
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        1
    } else {
        let prev = calcC(n - 1);
        proof {
            lemma_C_is_positive((n - 1) as nat);
            let C_n_minus_1 = C((n - 1) as nat);
            let four_n_minus_2 = 4 * (n as int) - 2;
            let n_plus_1 = (n as int) + 1;
            
            lemma_C_divisibility(n as nat);
            let numerator = four_n_minus_2 * (prev as int);
            assert(numerator >= 0);
            assert(n_plus_1 > 0);
            assert(div_is_exact(numerator, n_plus_1));
            assert((numerator / n_plus_1) as nat == C(n as nat));
        }
        let res_u128: u128 = ((4 * n as u128 - 2) * prev as u128) / (n as u128 + 1);
        res_u128 as u64
    }
}
// </vc-code>

fn main() {}

}