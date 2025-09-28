use vstd::prelude::*;

verus! {

/* 
HumanEvalX 3
You're given a list of deposit and withdrawal operations on a bank account that starts with zero balance. 
Your task is to detect if at any point the balance of account falls below zero, and at that point function 
should return True. Otherwise it should return False.
*/

spec fn sum(s: Seq<int>, n: nat) -> int
    recommends n <= s.len()
    decreases n
{
    if s.len() == 0 || n == 0 {
        0
    } else {
        s[0] + sum(s.subrange(1, s.len() as int), (n - 1) as nat)
    }
}

// <vc-helpers>
#[verifier::spinoff_prover]
proof fn sum_additive(s: Seq<int>, n: nat, m: nat)
    requires n <= s.len(), m <= s.len(), n + m <= s.len()
    ensures sum(s.subrange(0, n as int), n) + sum(s.subrange(n as int, s.len() as int), m) == sum(s, n + m)
    decreases n
{
    if n == 0 {
        assert(sum(s, n + m) == sum(s.subrange(n as int, s.len() as int), m));
    } else {
        sum_additive(s.subrange(1, s.len() as int), (n - 1) as nat, m);
        assert(s[0] + sum(s.subrange(1, s.len() as int), (n - 1) as nat) + sum(s.subrange(n as int, s.len() as int), m)
            == s[0] + sum(s.subrange(1, s.len() as int), ((n - 1) + m) as nat));
    }
}
// </vc-helpers>

// <vc-spec>
fn below_zero(ops: Seq<int>) -> (result: bool)
    ensures result <==> exists|n: nat| n <= ops.len() && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
{
    let ghost len_ghost: usize = ops.len().to_usize();
    let mut balance_ghost: int = 0int;
    let mut i_ghost: int = 0int;
    let mut found_ghost: bool = false;
    assert(balance_ghost == sum(ops, i_ghost as nat));
    assert(forall |j: nat| j < (i_ghost as nat) ==> sum(ops, j) >= 0);

    let mut balance: i64 = 0;
    let mut i: usize = 0;
    let mut found: bool = false;

    while i < len_ghost && !found
        invariant
            i_ghost as nat <= ops.len(),
            balance_ghost == sum(ops, i_ghost as nat),
            forall |j: nat| j < (i_ghost as nat) ==> sum(ops, j) >= 0,
            found_ghost == exists |k: nat| k < (i_ghost as nat) && sum(ops, k) < 0,
    {
        if balance_ghost + ops[i as int] < 0 {
            found_ghost = true;
            found = true;
        } else {
            balance_ghost = balance_ghost + ops[i as int];
            balance = balance + (ops[i as int] as i64);
            i = i + 1;
            i_ghost = i_ghost + 1int;
            assert(balance_ghost == sum(ops, i_ghost as nat));
        }
    }

    if found {
        return true;
    } else {
        assert(forall |n: nat| n <= ops.len() ==> sum(ops, n) >= 0);
        return false;
    }
}
// </vc-code>

fn main() {}

}