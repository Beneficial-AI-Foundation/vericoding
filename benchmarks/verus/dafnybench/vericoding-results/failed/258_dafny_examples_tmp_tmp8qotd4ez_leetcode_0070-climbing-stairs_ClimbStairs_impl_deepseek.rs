use vstd::prelude::*;

verus! {

spec fn stairs(n: nat) -> nat
    decreases n
{
    if n <= 1 { 1 } else { stairs((n - 2) as nat) + stairs((n - 1) as nat) }
}

// A simple specification

// <vc-helpers>
proof fn lemma_stairs_monotonic(i: nat, j: nat)
    requires i <= j,
    ensures stairs(i) <= stairs(j),
    decreases j
{
    if i < j {
        lemma_stairs_monotonic(i, (j - 1) as nat);
        if j >= 2 {
            lemma_stairs_values(j);
        }
    }
}

proof fn lemma_stairs_values(n: nat)
    ensures
        if n == 0 { stairs(n) == 1 } else
        if n == 1 { stairs(n) == 1 } else
        { stairs(n) == stairs((n - 2) as nat) + stairs((n - 1) as nat) },
    decreases n
{
    if n >= 2 {
        lemma_stairs_values((n - 2) as nat);
        lemma_stairs_values((n - 1) as nat);
    }
}

proof fn lemma_stairs_nonzero(n: nat)
    ensures stairs(n) > 0,
    decreases n
{
    if n >= 2 {
        lemma_stairs_nonzero((n - 2) as nat);
        lemma_stairs_nonzero((n - 1) as nat);
    } else {
        // Base cases: n=0 and n=1 both return 1 > 0
    }
}

proof fn lemma_stairs_ge_1(n: nat)
    ensures stairs(n) >= 1,
    decreases n
{
    lemma_stairs_nonzero(n);
}

proof fn lemma_stairs_bounds(n: nat)
    ensures stairs(n) <= u32::MAX as nat,
    decreases n
{
    if n >= 2 {
        lemma_stairs_bounds((n - 2) as nat);
        lemma_stairs_bounds((n - 1) as nat);
        assert(stairs(n) == stairs((n - 2) as nat) + stairs((n - 1) as nat));
        assert(stairs((n - 2) as nat) <= u32::MAX as nat);
        assert(stairs((n - 1) as nat) <= u32::MAX as nat);
        assert(stairs((n - 2) as nat) + stairs((n - 1) as nat) <= u32::MAX as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn climb_stairs(n: u32) -> (r: u32)
    requires n >= 0
    ensures r == stairs(n as nat)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 1;
    }
    let mut a: u32 = 1;
    let mut b: u32 = 1;
    let mut i: u32 = 2;
    while i <= n
        invariant
            i <= n + 1,
            a == stairs((i - 2) as nat),
            b == stairs((i - 1) as nat),
        decreases (n + 1 - i)
    {
        proof {
            lemma_stairs_bounds((i - 1) as nat);
            lemma_stairs_bounds((i - 2) as nat);
            assert(a <= u32::MAX);
            assert(b <= u32::MAX);
            assert(a <= u32::MAX - b);
        }
        let next: u32 = a + b;
        proof {
            lemma_stairs_values(i as nat);
            assert(next as nat == stairs((i - 2) as nat) + stairs((i - 1) as nat));
            assert(stairs(i as nat) == stairs((i - 2) as nat) + stairs((i - 1) as nat));
            assert(next as nat == stairs(i as nat));
        }
        b = a;
        a = next;
        i = i + 1;
    }
    if n == 1 {
        b
    } else {
        a
    }
}
// </vc-code>

fn main() {
}

}