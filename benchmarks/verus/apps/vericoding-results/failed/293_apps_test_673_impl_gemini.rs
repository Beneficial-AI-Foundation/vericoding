// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k > 0
}

spec fn is_correct_result(n: int, k: int, result: int) -> bool 
    recommends k > 0
{
    result > n && result % k == 0 && forall|x: int| n < x < result ==> #[trigger] (x % k) != 0
}
// </vc-preamble>

// <vc-helpers>
#[verus::proof]
fn lemma_smallest_multiple_gap(base: int, k: int)
    requires
        k > 0,
        base % k == 0,
    ensures
        forall|x: int| base < x < base + k ==> #[trigger] (x % k) != 0,
{
    assert forall|x: int| base < x < base + k implies #[trigger] (x % k) != 0 by {
        if x % k == 0 {
            vstd::arithmetic::mod_prelude::lemma_mod_sub_multiples(x, base, k);
            assert((x - base) % k == 0);

            assert(0 < x - base < k) by {
                assert(x > base);
                assert(x - base > 0);
                assert(x < base + k);
                assert(x - base < k);
            };

            vstd::arithmetic::mod_prelude::lemma_rem_is_id_if_in_range(x - base, k);
            assert((x - base) % k == x - base);
            
            assert(x - base > 0);
            assert((x - base) % k != 0);
            
            assert(false);
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires valid_input(n as int, k as int)
    ensures is_correct_result(n as int, k as int, result as int)
// </vc-spec>
// <vc-code>
{
    let n_int = n as int;
    let k_int = k as int;

    let result_int = n_int - (n_int % k_int) + k_int;
    
    proof {
        let base_mult = n_int - (n_int % k_int);

        // Prove base_mult is a multiple of k_int
        vstd::arithmetic::div_mod::lemma_div_rem(n_int, k_int);
        assert(base_mult == k_int * (n_int / k_int));
        vstd::arithmetic::div_mod::lemma_mod_of_mul(n_int / k_int, k_int);
        assert(base_mult % k_int == 0);

        // Prove result_int is a multiple of k_int
        assert(result_int == base_mult + k_int);
        vstd::arithmetic::mod_prelude::lemma_mod_add(base_mult, k_int, k_int);
        assert(result_int % k_int == (base_mult % k_int + k_int % k_int) % k_int);
        assert(result_int % k_int == 0);

        // Prove result_int > n_int
        vstd::arithmetic::mod_prelude::lemma_rem_bound(n_int, k_int);
        assert(n_int % k_int < k_int);
        assert(k_int - (n_int % k_int) > 0);
        assert(result_int > n_int);

        // Prove minimality using the helper lemma
        lemma_smallest_multiple_gap(base_mult, k_int);

        assert(base_mult <= n_int);
        assert forall|x: int| n_int < x < result_int implies (x % k_int) != 0 by {
            assert(base_mult <= n_int < x < result_int);
            assert(base_mult < x);
        }
    }

    let result = result_int as i8;
    result
}
// </vc-code>


}

fn main() {}