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
proof fn sum_prefix_lemma(s: Seq<int>, i: nat, j: nat)
    requires i <= j <= s.len()
    ensures sum(s, j) == sum(s, i) + sum(s.subrange(i as int, s.len() as int), (j - i) as nat)
    decreases j - i
{
    if i == j {
        assert(sum(s, i) == sum(s, j));
        assert(sum(s.subrange(i as int, s.len() as int), 0) == 0);
    } else if i == 0 {
        if j == 0 {
            // base case handled above
        } else {
            sum_prefix_lemma(s.subrange(1, s.len() as int), 0, (j - 1) as nat);
        }
    } else {
        sum_prefix_lemma(s.subrange(1, s.len() as int), (i - 1) as nat, (j - 1) as nat);
    }
}

proof fn sum_additive(s: Seq<int>, i: nat)
    requires i < s.len()
    ensures sum(s, i + 1) == sum(s, i) + s[i as int]
    decreases i
{
    if i == 0 {
        assert(sum(s, 1) == s[0] + sum(s.subrange(1, s.len() as int), 0));
        assert(sum(s.subrange(1, s.len() as int), 0) == 0);
        assert(sum(s, 0) == 0);
    } else {
        sum_additive(s.subrange(1, s.len() as int), (i - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn below_zero(ops: Seq<int>) -> (result: bool)
    ensures result <==> exists|n: nat| n <= ops.len() && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
{
    let mut running_sum: int = 0;
    let mut i: usize = 0;
    
    while i <= ops.len()
        invariant 
            0 <= i <= ops.len(),
            running_sum == sum(ops, i as nat)
    {
        if running_sum < 0 {
            return true;
        }
        
        if i == ops.len() {
            break;
        }
        
        proof {
            sum_additive(ops, i as nat);
        }
        
        running_sum = running_sum + ops[i as int];
        i = i + 1;
    }
    
    false
}
// </vc-code>

fn main() {
}

}