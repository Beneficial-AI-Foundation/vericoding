use vstd::prelude::*;

verus! {

spec fn f2(n: nat) -> nat 
    decreases n
{
    if n == 0 { 0 }
    else { 5 * f2(n / 3) + n % 4 }
}

// <vc-helpers>
spec fn rem_is_less_than_4(n: u32) -> bool {
    n % 4 < 4
}

proof fn lemma_rem_is_less_than_4(n: u32)
    ensures
        rem_is_less_than_4(n),
{
    assert(n % 4 < 4);
}

spec fn div_by_3_decreases_nat(n: nat) -> bool {
    n / 3 < n
}

proof fn lemma_div_by_3_decreases_nat(n: nat)
    requires
        0 < n,
    ensures
        div_by_3_decreases_nat(n),
{
    assert(n / 3 < n);
}

spec fn div_by_3_decreases(n: u32) -> bool {
    div_by_3_decreases_nat(n as nat)
}

proof fn lemma_div_by_3_decreases(n: u32)
    requires
        0 < n,
    ensures
        div_by_3_decreases(n),
{
    lemma_div_by_3_decreases_nat(n as nat);
}

proof fn lemma_f2_recurrence_nat(n: nat)
    ensures
        f2(n) == if n == 0 { 0 } else { 5 * f2(n / 3) + n % 4 },
{
    reveal(f2);
}

proof fn lemma_f2_recurrence(n: u32)
    ensures
        f2(n as nat) == if n == 0 { 0 } else { 5 * f2((n / 3) as nat) + (n % 4) },
{
    lemma_f2_recurrence_nat(n as nat);
}
// </vc-helpers>

// <vc-spec>
fn mod2(n: u32) -> (a: u32)
    ensures a == f2(n as nat)
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_f2_recurrence(n);
    }
    if n == 0 {
        0
    } else {
        proof {
            lemma_div_by_3_decreases(n);
        }
        let next_val = mod2(n / 3);
        5 * next_val + (n % 4)
    }
}
// </vc-code>

fn main() {}

}