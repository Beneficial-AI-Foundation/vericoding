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
spec fn sum_prefix(s: Seq<int>, n: nat) -> int
    decreases n
    when n <= s.len()
{
    if n == 0 {
        0
    } else {
        s[n - 1] + sum_prefix(s.subrange(0, (n - 1) as int), (n - 1) as nat)
    }
}

proof fn sum_lemmas(ops: Seq<int>, i: nat)
    requires i <= ops.len()
    ensures sum(ops, i) == sum_prefix(ops, i)
    decreases i
{
    if i == 0 {
        assert(sum(ops,0) == 0);
        assert(sum_prefix(ops,0) == 0);
    } else {
        assert(i > 0);
        assert(ops.len() >= i); // This is needed to satisfy recommends of sum
        sum_lemmas(ops.subrange(0, (i-1) as int), (i-1) as nat);
        assert(sum_prefix(ops, i) == ops[(i-1) as int] + sum_prefix(ops.subrange(0, (i-1) as int), (i-1) as nat));
        assert(sum(ops, i) == ops[(i-1) as int] + sum(ops.subrange(0, (i-1) as int), (i-1) as nat));
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
    let mut i: nat = 0;

    while i < ops.len()
        invariant 0 <= i <= ops.len()
        invariant balance == sum_prefix(ops.subrange(0, i as int), i)
    {
        let op = ops@i;
        balance = balance + op;
        i = i + 1;
        if balance < 0 {
            proof {
                assert(i > 0);
                assert(ops.len() >= i);
                sum_lemmas(ops.subrange(0, i as int), i);
                assert(sum(ops.subrange(0, i as int), i) == balance);
            }
            return true;
        }
    }
    return false;
}
// </vc-code>

fn main() {}

}