use vstd::prelude::*;

verus! {

/* 
* Formal verification of O(n) and O(log n) algorithms to calculate the natural
* power of a real number (x^n), illustrating the usage of lemmas.
* FEUP, M.EIC, MFS, 2021/22.
*/

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
spec fn power(x: int, n: nat) -> int
    decreases n
{
    if n == 0 { 1 } else { x * power(x, (n-1) as nat) }
}

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).

// <vc-helpers>
lemma fn induction_on_nat_range(
    lo: nat,
    hi: nat,
    P: spec fn(nat) -> bool,
)
    requires
        hi >= lo,
        forall|i: nat| lo <= i < hi ==> #[trigger] P(i) ==> P((i + 1) as nat), // Induction step
        P(lo), // Base case
    ensures
        forall|i: nat| lo <= i <= hi ==> P(i),
{
    if lo == hi {
        assert(P(lo));
    } else {
        assert(P(lo));
        induction_on_nat_range(
            (lo + 1) as nat,
            hi,
            P,
        );
        assert(forall|i: nat| (lo + 1) as nat <= i <= hi ==> P(i));
        assert(forall|i: nat| lo <= i <= hi ==> P(i));
    }
}
// </vc-helpers>

// <vc-spec>
fn power_iter(b: i32, n: u32) -> (p: i32)
    ensures p as int == power(b as int, n as nat)
// </vc-spec>
// <vc-code>
{
    let mut p: i32 = 1;
    let mut i: u32 = 0;

    while i < n
        invariant
            i <= n,
            p as int == power(b as int, i as nat),
    {
        p = p * b;
        i = i + 1;
    }
    p
}
// </vc-code>

// Recursive version, imperative, with time and space complexity O(log n).

// A simple test case to make sure the specification is adequate.

fn main() {}

}