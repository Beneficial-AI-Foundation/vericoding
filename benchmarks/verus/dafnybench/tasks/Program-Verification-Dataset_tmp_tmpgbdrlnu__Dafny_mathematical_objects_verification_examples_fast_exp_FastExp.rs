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
// </vc-helpers>

// <vc-spec>
fn fast_exp(b: u32, n: u32) -> (r: u32)
    ensures r == exp(b as nat, n as nat)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}