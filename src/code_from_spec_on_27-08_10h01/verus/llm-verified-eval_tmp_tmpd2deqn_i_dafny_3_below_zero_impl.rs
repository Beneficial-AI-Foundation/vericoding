use vstd::prelude::*;

verus! {

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
spec fn sum_monotonic(s: Seq<int>, n1: nat, n2: nat) -> bool
    recommends n1 <= n2 <= s.len()
{
    sum(s, n1) <= sum(s, n2) || exists|i: nat| n1 <= i < n2 && s[i as int] < 0
}

proof fn sum_step_lemma(s: Seq<int>, n: nat)
    requires n < s.len()
    ensures sum(s, n + 1) == sum(s, n) + s[n as int]
    decreases s.len() - n
{
    if n == 0 {
        assert(sum(s, 1) == s[0] + sum(s.subrange(1, s.len() as int), 0));
        assert(sum(s.subrange(1, s.len() as int), 0) == 0);
        assert(sum(s, 0) == 0);
    } else {
        let s_tail = s.subrange(1, s.len() as int);
        assert(sum(s, n + 1) == s[0] + sum(s_tail, n));
        assert(sum(s, n) == s[0] + sum(s_tail, (n - 1) as nat));
        sum_step_lemma(s_tail, (n - 1) as nat);
        assert(sum(s_tail, n) == sum(s_tail, (n - 1) as nat) + s_tail[(n - 1) as int]);
        assert(s_tail[(n - 1) as int] == s[n as int]);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn below_zero(ops: Seq<int>) -> (result: bool)
    ensures result <==> exists|n: nat| n <= ops.len() && sum(ops, n) < 0
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut running_sum: int = 0;
    let mut i: usize = 0;
    
    while i < ops.len()
        invariant 0 <= i <= ops.len()
        invariant running_sum == sum(ops, i as nat)
        invariant forall|j: nat| j < i ==> sum(ops, j + 1) >= 0
    {
        running_sum = running_sum + ops[i as int];
        
        proof {
            sum_step_lemma(ops, i as nat);
            assert(sum(ops, (i + 1) as nat) == sum(ops, i as nat) + ops[i as int]);
        }
        
        if running_sum < 0 {
            proof {
                assert(sum(ops, (i + 1) as nat) < 0);
                assert(exists|n: nat| n <= ops.len() && sum(ops, n) < 0);
            }
            return true;
        }
        
        i = i + 1;
    }
    
    proof {
        assert(forall|j: nat| j <= ops.len() ==> sum(ops, j) >= 0);
        assert(!exists|n: nat| n <= ops.len() && sum(ops, n) < 0);
    }
    
    false
}
// </vc-code>

fn main() {
}

}