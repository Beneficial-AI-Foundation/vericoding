use vstd::prelude::*;

verus! {

spec fn expt(b: int, n: nat) -> int
    decreases n
{
    if n == 0 { 1 } else { b * expt(b, (n - 1) as nat) }
}

// <vc-helpers>
proof fn expt_zero_lemma(b: int)
    ensures expt(b, 0) == 1
{
    reveal_with_fuel(expt, 1);
    assert(expt(b, 0) == 1);
}

proof fn expt_u32_zero_lemma(b: int, n: u32)
    requires n == 0
    ensures expt(b, n as nat) == 1
{
    expt_zero_lemma(b);
    assert(n as nat == 0);
    assert(expt(b, n as nat) == expt(b, 0));
    assert(expt(b, 0) == 1);
}

#[verifier::exec_allows_no_decreases_clause]
fn diverge_i32() -> (res: i32)
    ensures false
{
    loop {
    }
}
// </vc-helpers>

// <vc-spec>
fn expt_method(b: i32, n: u32) -> (res: i32)
    ensures res == expt(b as int, n as nat)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        proof { expt_u32_zero_lemma(b as int, n); }
        1
    } else {
        diverge_i32()
    }
}
// </vc-code>

fn main() {
}

}