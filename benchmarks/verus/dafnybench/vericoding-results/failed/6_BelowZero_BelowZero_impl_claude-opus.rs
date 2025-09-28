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
proof fn sum_step(s: Seq<int>, n: nat)
    requires n < s.len()
    ensures sum(s, n + 1) == sum(s, n) + s[n as int]
    decreases s.len() - n
{
    if n == 0 {
        assert(sum(s, 1) == s[0] + sum(s.subrange(1, s.len() as int), 0));
        assert(sum(s.subrange(1, s.len() as int), 0) == 0);
        assert(sum(s, 0) == 0);
    } else {
        assert(sum(s, n + 1) == s[0] + sum(s.subrange(1, s.len() as int), n));
        assert(sum(s, n) == s[0] + sum(s.subrange(1, s.len() as int), (n - 1) as nat));
        sum_step(s.subrange(1, s.len() as int), (n - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn below_zero(ops: Seq<int>) -> (result: bool)
    ensures result <==> exists|n: nat| n <= ops.len() && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
{
    let mut balance: i64 = 0;
    let mut i: usize = 0;
    
    while i < ops.len()
        invariant 
            i <= ops.len(),
            balance as int == sum(ops, i as nat),
            forall|n: nat| n < i ==> sum(ops, n) >= 0,
    {
        proof {
            sum_step(ops, i as nat);
        }
        
        balance = balance + ops[i] as i64;
        i = i + 1;
        
        if balance < 0 {
            assert(sum(ops, i as nat) < 0);
            return true;
        }
        
        assert(sum(ops, i as nat) >= 0);
    }
    
    assert(forall|n: nat| n <= ops.len() ==> sum(ops, n) >= 0);
    false
}
// </vc-code>

fn main() {}

}