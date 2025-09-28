// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn sum_from_one_to_n(n: int) -> int
    recommends n >= 1
{
    n * (n + 1) / 2
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_sum_increment(n: int)
    requires
        n >= 1,
    ensures
        sum_from_one_to_n(n) == sum_from_one_to_n(n - 1) + n,
{
    assert_by(sum_from_one_to_n(n) == sum_from_one_to_n(n - 1) + n, {
        assert((n * (n - 1)) % 2 == 0) by(nonlinear_arith)
            requires n % 2 == 0 || (n - 1) % 2 == 0;
        vstd::arithmetic::div_mod::lemma_div_multiples(n * (n - 1), 2 * n, 2);
    });
}

proof fn lemma_sum_monotonicity(j: int, k: int)
    requires
        0 <= j,
        j <= k,
    ensures sum_from_one_to_n(j) <= sum_from_one_to_n(k)
{
    assert(sum_from_one_to_n(j) <= sum_from_one_to_n(k)) by(nonlinear_arith)
        requires
            0 <= j,
            j <= k,
    {}
}
// </vc-helpers>

// <vc-spec>
fn sum_to_n(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == sum_from_one_to_n(n as int)
// </vc-spec>
// <vc-code>
{
    let mut sum: i8 = 0;
    let mut i: u8 = 1;
    let n_u8 = n as u8;

    while i <= n_u8
        invariant
            1 <= i,
            i <= n_u8 + 1,
            sum as int == sum_from_one_to_n((i - 1) as int),
        decreases (n_u8 - i)
    {
        proof {
            lemma_sum_increment(i as int);
            lemma_sum_monotonicity(i as int, n as int);
        }
        sum = sum + (i as i8);
        i = i + 1;
    }
    sum
}
// </vc-code>


}

fn main() {}