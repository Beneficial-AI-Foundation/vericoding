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
proof fn sum_prefix_property(s: Seq<int>, n: nat, m: nat)
    requires n <= m <= s.len()
    ensures sum(s, n) == sum(s.subrange(0, m as int), n)
    decreases n
{
    if n == 0 {
    } else if s.len() == 0 {
    } else {
        sum_prefix_property(s.subrange(1, s.len() as int), (n-1) as nat, (m-1) as nat);
    }
}

proof fn sum_monotonic(s: Seq<int>, n: nat)
    requires n < s.len()
    ensures sum(s, n+1) == sum(s, n) + s[n as int]
    decreases n
{
    if n == 0 {
        assert(sum(s, 1) == s[0] + sum(s.subrange(1, s.len() as int), 0));
        assert(sum(s.subrange(1, s.len() as int), 0) == 0);
        assert(sum(s, 0) == 0);
    } else {
        sum_monotonic(s.subrange(1, s.len() as int), (n-1) as nat);
        assert(sum(s.subrange(1, s.len() as int), n) == sum(s.subrange(1, s.len() as int), (n-1) as nat) + s.subrange(1, s.len() as int)[(n-1) as int]);
        assert(s.subrange(1, s.len() as int)[(n-1) as int] == s[n as int]);
    }
}

proof fn sum_empty(n: nat)
    ensures sum(Seq::<int>::empty(), n) == 0
{
}
// </vc-helpers>

// <vc-spec>
fn below_zero(ops: Seq<int>) -> (result: bool)
    ensures result <==> exists|n: nat| n <= ops.len() && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
{
    if ops.len() == 0nat {
        return false;
    }
    
    let mut balance = 0;
    let mut i = 0usize;
    
    while i < ops.len() as usize
        invariant 
            0 <= i <= ops.len(),
            balance == sum(ops, i as nat),
            forall|k: nat| k < i ==> sum(ops, k) >= 0
    {
        if balance < 0 {
            return true;
        }
        
        balance = balance + ops[i as int];
        
        proof {
            sum_monotonic(ops, i as nat);
        }
        
        i = i + 1;
    }
    
    if balance < 0 {
        return true;
    }
    
    proof {
        assert(forall|k: nat| k <= ops.len() ==> sum(ops, k) >= 0);
    }
    
    false
}
// </vc-code>

fn main() {}

}