use vstd::prelude::*;

verus! {

spec fn fact(n: nat) -> nat 
    decreases n
{
    if n == 0 { 1 } else { n * fact((n - 1) as nat) }
}

// <vc-helpers>
proof fn fact_unfold(k: nat)
    ensures k > 0 ==> fact(k) == k * fact(k - 1)
    decreases k
{
    if k == 0 {
        // vacuous
    } else {
        // By the definition of `fact`, when k > 0, fact(k) == k * fact(k-1).
        assert(fact(k) == k * fact(k - 1));
    }
}
// </vc-helpers>

// <vc-spec>
fn factorial(n: u32) -> (res: u32)
    requires n <= 12  // to prevent overflow
    ensures res == fact(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut i: nat = 0;
    let mut acc: u32 = 1;

    while i < (n as nat)
        invariant i <= (n as nat);
        invariant (acc as nat) == fact(i);
        decreases ((n as nat) - i)
    {
        let old_i = i;
        let old_acc = acc;

        acc = old_acc * ((old_i + 1) as u32);
        i = old_i + 1;

        proof {
            assert(old_i <= (n as nat));
            assert((old_acc as nat) == fact(old_i));
            assert((acc as nat) == (old_acc as nat) * (old_i + 1));
            assert(old_i + 1 > 0);
            fact_unfold(old_i + 1);
            assert(fact(old_i + 1) == (old_i + 1) * fact(old_i));
            assert((acc as nat) == fact(old_i + 1));
        }
    }

    proof {
        assert(!(i < (n as nat)));
        assert(i >= (n as nat));
        assert(i <= (n as nat));
        assert(i == (n as nat));
        assert((acc as nat) == fact(i));
        assert((acc as nat) == fact(n as nat));
    }

    acc
}
// </vc-code>

fn main() {}

}