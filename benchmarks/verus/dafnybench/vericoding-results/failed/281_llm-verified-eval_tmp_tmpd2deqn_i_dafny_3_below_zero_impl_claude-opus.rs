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
proof fn sum_add_one(s: Seq<int>, n: nat)
    requires n < s.len()
    ensures sum(s, n + 1) == sum(s, n) + s[n as int]
    decreases s.len() - n
{
    if n == 0 {
        assert(sum(s, 1) == s[0] + sum(s.subrange(1, s.len() as int), 0));
        assert(sum(s.subrange(1, s.len() as int), 0) == 0);
        assert(sum(s, 0) == 0);
    } else {
        assert(sum(s, (n + 1) as nat) == s[0] + sum(s.subrange(1, s.len() as int), n as nat));
        assert(sum(s, n) == s[0] + sum(s.subrange(1, s.len() as int), (n - 1) as nat));
        sum_add_one(s.subrange(1, s.len() as int), (n - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn below_zero(ops: Seq<int>) -> (result: bool)
    ensures result <==> exists|n: nat| n <= ops.len() && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut running_sum: i64 = 0;
    
    while i < ops.len()
        invariant
            i <= ops.len(),
            running_sum == sum(ops, i as nat),
            forall|j: nat| j < i ==> sum(ops, j) >= 0,
    {
        proof {
            sum_add_one(ops, i as nat);
        }
        
        let val = ops[i as int];
        running_sum = running_sum + val;
        i = i + 1;
        
        if running_sum < 0 {
            assert(sum(ops, i as nat) < 0);
            return true;
        }
    }
    
    assert(forall|n: nat| n <= ops.len() ==> sum(ops, n) >= 0);
    false
}
// </vc-code>

fn main() {
}

}