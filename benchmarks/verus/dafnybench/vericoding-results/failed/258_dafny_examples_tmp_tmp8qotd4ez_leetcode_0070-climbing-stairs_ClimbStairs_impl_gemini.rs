// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn stairs(n: nat) -> nat
    decreases n
{
    if n <= 1 { 1 } else { stairs((n - 2) as nat) + stairs((n - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): No changes, just resubmitting with comment. */
proof fn lemma_stairs_positive(k: nat)
    ensures stairs(k) >= 1
    decreases k
{
    if k >= 2 {
        lemma_stairs_positive((k - 1) as nat);
        lemma_stairs_positive((k - 2) as nat);
    }
}

proof fn stairs_is_monotonic(m: nat, n: nat)
    requires m <= n
    ensures stairs(m) <= stairs(n)
    decreases n
{
    if n >= 2 && m < n {
        stairs_is_monotonic(m, (n - 1) as nat);
        lemma_stairs_positive((n - 2) as nat);
    }
}

proof fn stairs_recursive_def(i: nat)
    requires i >= 2
    ensures stairs(i) == stairs((i - 2) as nat) + stairs((i - 1) as nat)
{
}
// </vc-helpers>

// <vc-spec>
fn climb_stairs(n: u32) -> (r: u32)
    requires n >= 0
    ensures r == stairs(n as nat)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): changed variable types from ghost `int` to executable `u32` */
    if n <= 1 {
        return 1;
    }

    let mut a: u32 = 1;
    let mut b: u32 = 1;
    let mut i: u32 = 2;

    while i <= n
        invariant
            n > 1,
            2 <= i <= n + 1,
            a as nat == stairs((i - 2) as nat),
            b as nat == stairs((i - 1) as nat),
        decreases n - i
    {
        proof {
            stairs_recursive_def(i as nat);
        }

        let temp = b;
        b = a + b;
        a = temp;
        i = i + 1;
    }
    
    b
}
// </vc-code>

}
fn main() {}