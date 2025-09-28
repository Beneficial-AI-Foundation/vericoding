use vstd::prelude::*;

verus! {

spec fn R(n: nat) -> nat
    decreases n
{
    if n == 0 { 
        0nat 
    } else if R((n-1) as nat) > n { 
        (R((n-1) as nat) - n) as nat
    } else { 
        (R((n-1) as nat) + n) as nat
    }
}

// <vc-helpers>
spec fn R_alt(n: nat) -> bool
    decreases n
{
    if n == 0 {
        true
    } else {
        &&& R_alt((n - 1) as nat)
        &&& (R((n - 1) as nat) > n) == (R(n) == (R((n - 1) as nat) - n) as nat)
        &&& (R((n - 1) as nat) <= n) == (R(n) == (R((n - 1) as nat) + n) as nat)
    }
}

proof fn lemma_R_alt_forall()
    ensures forall |n: nat| #[trigger] R_alt(n)
{
    reveal_with_fuel(R, 2);
    assert forall |n: nat| R_alt(n) by {
        if n > 0 {
            assert(R_alt((n - 1) as nat));
            assert(R((n-1) as nat) > n || R((n-1) as nat) <= n);
        }
    }
}

proof fn lemma_R_decreases(n: nat)
    requires n > 0
    ensures R(n) <= R((n - 1) as nat) + n
{
    reveal_with_fuel(R, 2);
    if R((n-1) as nat) > n {
        assert(R(n) == (R((n-1) as nat) - n) as nat);
        assert(R(n) <= R((n-1) as nat) + n);
    } else {
        assert(R(n) == (R((n-1) as nat) + n) as nat);
        assert(R(n) <= R((n-1) as nat) + n);
    }
}

proof fn lemma_R_step(i: u64, r: u64)
    requires r == R(i as nat)
    ensures (if r > (i + 1) { r - (i + 1) } else { r + (i + 1) }) == R((i + 1) as nat)
{
    reveal_with_fuel(R, 2);
    assert(R_alt(i as nat));
    assert(R_alt((i + 1) as nat));
    assert(R(i as nat) > (i + 1) || R(i as nat) <= (i + 1));
}
// </vc-helpers>

// <vc-spec>
fn calcR(n: u64) -> (r: u64)
    ensures r == R(n as nat)
// </vc-spec>
// <vc-code>
{
    lemma_R_alt_forall();
    let mut i: u64 = 0;
    let mut r: u64 = 0;
    while i < n
        invariant r == R(i as nat)
    {
        let next_i = i + 1;
        if r > next_i {
            lemma_R_step(i, r);
            r = r - next_i;
        } else {
            lemma_R_step(i, r);
            r = r + next_i;
        }
        i = next_i;
    }
    r
}
// </vc-code>

fn main() {}

}