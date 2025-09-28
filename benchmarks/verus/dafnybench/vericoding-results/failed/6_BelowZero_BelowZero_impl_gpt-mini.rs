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
proof fn sum_succ(s: Seq<int>, n: nat)
    requires n + 1 <= s.len()
    ensures sum(s, n + 1) == sum(s, n) + s@[n]
    decreases n
{
    if n == 0 {
        // sum(s,1) == s@[0], sum(s,0) == 0
        assert(sum(s, 1) == s@[0]);
        assert(sum(s, 0) + s@[0] == s@[0]);
    } else {
        let sub = s.subrange(1, s.len());
        // n > 0 implies n - 1 is a valid parameter for sub
        sum_succ(sub, n - 1);
        // Expand definitions (by the definition of sum)
        // sum(s, n+1) = s@[0] + sum(sub, n)
        // sum(s, n)   = s@[0] + sum(sub, n-1)
        assert(sum(s, n + 1) == s@[0] + sum(sub, n));
        assert(sum(s, n) == s@[0] + sum(sub, n - 1));
        // From recursive call: sum(sub, n) == sum(sub, n-1) + sub@[n-1]
        assert(sum(sub, n) == sum(sub, n - 1) + sub@[n - 1]);
        // combine equalities
        assert(sum(s, n + 1) == s@[0] + (sum(sub, n - 1) + sub@[n - 1]));
        assert(sum(s, n + 1) == (s@[0] + sum(sub, n - 1)) + sub@[n - 1]);
        assert(sum(s, n + 1) == sum(s, n) + sub@[n - 1]);
        // relate sub@[n-1] to s@[n]
        assert(sub@[n - 1] == s@[n]);
        assert(sum(s, n + 1) == sum(s, n) + s@[n]);
    }
}
// </vc-helpers>

// <vc-spec>
fn below_zero(ops: Seq<int>) -> (result: bool)
    ensures result <==> exists|n: nat| n <= ops.len() && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
{
    let mut i: nat = 0;
    let mut bal: int = 0;
    while i < ops.len()
        invariant i <= ops.len();
        invariant bal == sum(ops, i);
        invariant forall |j: nat| j <= i ==> #[trigger] sum(ops, j) >= 0;
        decreases ops.len() - i;
    {
        let op = ops[@i];
        let new_bal = bal + op;
        if new_bal < 0 {
            proof {
                // i < ops.len() so i + 1 <= ops.len()
                assert(i + 1 <= ops.len());
                // sum(ops, i+1) == sum(ops, i) + ops@[i] by lemma
                sum_succ(ops, i);
                assert(sum(ops, i + 1) == sum(ops, i) + ops@[i]);
                // bal == sum(ops,i)
                assert(bal == sum(ops, i));
                // therefore sum(ops, i+1) == new_bal
                assert(sum(ops, i + 1) == new_bal);
                // and new_bal < 0 holds here
                assert(sum(ops, i + 1) < 0);
            }
            return true;
        } else {
            // prepare invariants for next iteration: i' = i+1, bal' = new_bal
            proof {
                // show i+1 <= ops.len()
                assert(i + 1 <= ops.len());
                // use lemma to show sum(ops, i+1) == sum(ops,i) + ops@[i]
                sum_succ(ops, i);
                assert(sum(ops, i + 1) == sum(ops, i) + ops@[i]);
                // hence new_bal == sum(ops, i+1)
                assert(new_bal == sum(ops, i + 1));
                // maintain non-negativity of all prefixes up to i+1
                // for j <= i we already have sum(ops,j) >= 0
                // for j == i+1, sum(ops,i+1) == new_bal and new_bal >= 0 here
                assert(new_bal >= 0);
            }
            bal = new_bal;
            i = i + 1;
        }
    }
    proof {
        // loop exited with i >= ops.len(), and invariant i <= ops.len() so i == ops.len()
        assert(i >= ops.len());
        assert(i <= ops.len());
        assert(i == ops.len());
        // invariant gives forall j <= i ==> sum(ops,j) >= 0, with i == ops.len()
        assert(forall|j: nat| j <= ops.len() ==> sum(ops, j) >= 0);
    }
    false
}
// </vc-code>

fn main() {}

}