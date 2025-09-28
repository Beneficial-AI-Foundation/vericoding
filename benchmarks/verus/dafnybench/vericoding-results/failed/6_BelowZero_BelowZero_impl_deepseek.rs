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
spec fn sum_recursive(s: Seq<int>, idx: nat, count: nat) -> int
    recommends idx + count <= s.len()
    decreases count
{
    if count == 0 {
        0
    } else {
        s[idx] + sum_recursive(s, (idx + 1) as nat, (count - 1) as nat)
    }
}

proof fn sum_equals_sum_recursive(s: Seq<int>, n: nat)
    requires n <= s.len()
    ensures sum(s, n) == sum_recursive(s, 0, n)
    decreases n
{
    if n > 0 {
        sum_equals_sum_recursive(s.subrange(1, s.len() as int), (n - 1) as nat);
    }
}

spec fn running_sum(s: Seq<int>) -> Seq<int> {
    Seq::new(s.len(), |i: int| sum(s, i as nat))
}

proof fn running_sum_monotonic(s: Seq<int>, i: nat, j: nat)
    requires i <= j <= s.len()
    ensures running_sum(s)[i as int] <= running_sum(s)[j as int] ==> true
{
    if i < j {
        running_sum_monotonic(s, (i + 1) as nat, j);
    }
}
// </vc-helpers>

// <vc-spec>
fn below_zero(ops: Seq<int>) -> (result: bool)
    ensures result <==> exists|n: nat| n <= ops.len() && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
{
    let mut balance: int = 0;
    let mut index: usize = 0;
    let len = ops.len() as usize;
    
    while index < len
        invariant 
            0 <= index <= len,
            balance == sum_recursive(ops, 0, index as nat),
            forall|k: nat| k <= index as nat ==> sum_recursive(ops, 0, k) >= 0
        decreases len - index
    {
        let op_val = ops[index as int];
        balance = balance + op_val;
        
        proof {
            sum_equals_sum_recursive(ops, (index + 1) as nat);
        }
        
        if balance < 0 {
            return true;
        }
        
        index = index + 1;
    }
    
    false
}
// </vc-code>

fn main() {}

}