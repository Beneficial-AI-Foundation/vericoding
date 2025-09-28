use vstd::prelude::*;

verus! {

spec fn f(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 }
    else if n % 2 == 0 { 1 + 2 * f(n / 2) }
    else { 2 * f(n / 2) }
}

// <vc-helpers>
proof fn lemma_f_inductive(n: nat)
    decreases n
{
    if n == 0 {
    } else if n % 2 == 0 {
        lemma_f_inductive(n / 2);
    } else {
        lemma_f_inductive(n / 2);
    }
}

proof fn lemma_f_properties(n: nat)
    decreases n
{
    lemma_f_inductive(n);
    if n == 0 {
        assert(f(n) == 1);
    } else if n % 2 == 0 {
        assert(f(n) == 1 + 2 * f(n / 2));
    } else {
        assert(f(n) == 2 * f(n / 2));
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_fn(n: u64) -> (a: u64)
    requires n >= 0,
    ensures a as nat == f(n as nat),
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        1
    } else if n % 2 == 0 {
        let m = n / 2;
        let res = mod_fn(m);
        proof {
            lemma_f_properties(m as nat);
        }
        1 + 2 * res
    } else {
        let m = n / 2;
        let res = mod_fn(m);
        proof {
            lemma_f_properties(m as nat);
        }
        2 * res
    }
}
// </vc-code>

fn main() {}

}