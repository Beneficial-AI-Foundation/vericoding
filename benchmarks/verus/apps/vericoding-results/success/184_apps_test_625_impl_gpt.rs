// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn alternating_sum(n: int) -> int
    recommends n > 0
    decreases n
{
    if n <= 0 { 0 }
    else if n == 1 { -1 }
    else { alternating_sum(n - 1) + (if n % 2 == 0 { n } else { -n }) }
}

spec fn valid_input(n: int) -> bool {
    n > 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed integer literal suffixes and clarified division-by-2 reasoning */
proof fn two_k_minus_one_div_two(k: int)
    ensures
        (2int * k - 1int) / 2int == k - 1int,
{
    assert(2int * k - 1int == 2int * (k - 1int) + 1int);
    assert(0int <= 1int && 1int < 2int);
    assert((2int * (k - 1int) + 1int) / 2int == k - 1int);
}

/* helper modified by LLM (iteration 3): fixed integer literal suffixes; shows (n-1)/2 equals n/2 for positive odd n */
proof fn half_same_odd_pos(n: int)
    requires
        n > 0int,
        n % 2int != 0int,
    ensures
        (n - 1int) / 2int == n / 2int,
{
    assert(0int <= n % 2int && n % 2int < 2int);
    assert(n % 2int == 1int);
    assert(n == (n / 2int) * 2int + n % 2int);
    assert(n - 1int == (n / 2int) * 2int);
    assert((n - 1int) / 2int == ((n / 2int) * 2int) / 2int);
    assert(((n / 2int) * 2int) / 2int == n / 2int);
}

/* helper modified by LLM (iteration 3): fixed integer literal suffixes; shows (n-1)/2 + 1 equals n/2 for positive even n */
proof fn half_inc_even_pos(n: int)
    requires
        n > 0int,
        n % 2int == 0int,
    ensures
        (n - 1int) / 2int + 1int == n / 2int,
{
    let q: int = n / 2int;
    assert(n == q * 2int + n % 2int);
    assert(n % 2int == 0int);
    assert(n == q * 2int);
    assert(n - 1int == 2int * q - 1int);
    two_k_minus_one_div_two(q);
    assert((n - 1int) / 2int == q - 1int);
    assert((n - 1int) / 2int + 1int == q);
}

/* helper modified by LLM (iteration 3): added parity toggle lemma for n-1 */
proof fn parity_toggle_sub1(n: int)
    ensures
        n % 2int == 0int ==> (n - 1int) % 2int != 0int,
        n % 2int != 0int ==> (n - 1int) % 2int == 0int,
{
    let q = n / 2int;
    let r = n % 2int;
    assert(0int <= r && r < 2int);
    assert(n == 2int * q + r);
    if r == 0int {
        assert(n % 2int == 0int);
        assert(n - 1int == 2int * q - 1int);
        assert(2int * q - 1int == 2int * (q - 1int) + 1int);
        assert((2int * (q - 1int) + 1int) % 2int == 1int);
        assert((n - 1int) % 2int != 0int);
    } else {
        assert(r == 1int);
        assert(n % 2int != 0int);
        assert(n - 1int == 2int * q + 1int - 1int);
        assert(n - 1int == 2int * q);
        assert((n - 1int) % 2int == 0int);
    }
}

/* helper modified by LLM (iteration 3): fixed integer literal suffixes and used parity toggle lemma in induction */
proof fn alt_sum_closed_form(n: int)
    requires
        n > 0int,
    ensures
        if n % 2int == 0int {
            alternating_sum(n) == n / 2int
        } else {
            alternating_sum(n) == n / 2int - n
        },
    decreases n
{
    if n == 1int {
        assert(alternating_sum(1int) == -1int);
        assert(1int % 2int != 0int);
        assert(1int / 2int == 0int);
        assert(1int / 2int - 1int == -1int);
    } else {
        alt_sum_closed_form(n - 1int);
        parity_toggle_sub1(n);
        if n % 2int == 0int {
            assert(alternating_sum(n) == alternating_sum(n - 1int) + n);
            assert((n - 1int) % 2int != 0int);
            assert(alternating_sum(n - 1int) == (n - 1int) / 2int - (n - 1int));
            assert(alternating_sum(n) == (n - 1int) / 2int - (n - 1int) + n);
            half_inc_even_pos(n);
            assert((n - 1int) / 2int + 1int == n / 2int);
            assert(alternating_sum(n) == n / 2int);
        } else {
            assert(alternating_sum(n) == alternating_sum(n - 1int) - n);
            assert((n - 1int) % 2int == 0int);
            assert(alternating_sum(n - 1int) == (n - 1int) / 2int);
            assert(alternating_sum(n) == (n - 1int) / 2int - n);
            half_same_odd_pos(n);
            assert((n - 1int) / 2int == n / 2int);
            assert(alternating_sum(n) == n / 2int - n);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures 
        result as int == alternating_sum(n as int) &&
        (n as int % 2 == 0 ==> result as int == n as int / 2) &&
        (n as int % 2 != 0 ==> result as int == n as int / 2 - n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): compute result in i8 and connect to spec via closed-form lemma */
    let result: i8 = if n % 2 == 0 { n / 2 } else { n / 2 - n };
    proof {
        let ghost ni: int = n as int;
        alt_sum_closed_form(ni);
        if n % 2 == 0 {
            assert((n as int) % 2int == 0int);
            assert(alternating_sum(ni) == ni / 2int);
            assert(result == n / 2);
            assert((n / 2) as int == ni / 2int);
            assert(result as int == alternating_sum(ni));
        } else {
            assert((n as int) % 2int != 0int);
            assert(alternating_sum(ni) == ni / 2int - ni);
            assert(result == n / 2 - n);
            assert((n / 2 - n) as int == ni / 2int - ni);
            assert(result as int == alternating_sum(ni));
        }
    }
    result
}
// </vc-code>


}

fn main() {}