// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(s: Seq<int>, i: nat) -> int
    recommends i <= s.len()
    decreases i
{
    if i == 0 { 0 } else { sum(s, (i - 1) as nat) + s[i - 1] }
}

spec fn exp(b: nat, n: nat) -> nat
    decreases n
{
    if n == 0 { 1nat } else { b * exp(b, (n - 1) as nat) }
}

spec fn bits(n: nat) -> Seq<bool>
    decreases n
{
    if n == 0 {
        seq![]
    } else {
        seq![n % 2 != 0].add(bits((n / 2) as nat))
    }
}

spec fn from_bits(s: Seq<bool>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        (if s[0] { 1nat } else { 0nat }) + 2nat * from_bits(s.subrange(1, s.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): reviewed, no logic changes */
proof fn lemma_exp_is_power_of_square(b: nat, k: nat)
    ensures exp(b, 2 * k) == exp(b * b, k)
    decreases k
{
    if k > 0 {
        lemma_exp_is_power_of_square(b, (k - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn fast_exp(b: u32, n: u32) -> (r: u32)
    ensures r == exp(b as nat, n as nat)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed compilation error */
    let ghost b_nat = b as nat;
    let ghost n_nat = n as nat;

    if n == 0 {
        return 1;
    }

    let mut r: u32 = 1;
    let mut power: u32 = b;
    let mut i: u32 = n;

    while i > 1
        invariant
            i > 0,
            n > 0,
            exp(b_nat, n_nat) == (r as nat) * exp(power as nat, i as nat),
        decreases i
    {
        proof {
            lemma_exp_is_power_of_square(power as nat, (i / 2) as nat);
        }

        if i % 2 == 1 {
            r = r * power;
        }

        power = power * power;
        i = i / 2;
    }

    r * power
}
// </vc-code>

}
fn main() {}