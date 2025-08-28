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
proof fn sum_monotonic(s: Seq<int>, n1: nat, n2: nat)
    requires
        n1 <= n2,
        n2 <= s.len(),
    ensures
        sum(s, n1) <= sum(s, n2),
    decreases n2
{
    if n1 == n2 {
        assert(sum(s, n1) == sum(s, n2));
    } else if n1 == 0 {
        assert(sum(s, 0) == 0);
        assert(sum(s, n2) >= 0 || sum(s, n2) <= 0);
    } else {
        sum_monotonic(s.subrange(1, s.len() as int), (n1 - 1) as nat, (n2 - 1) as nat);
        assert(sum(s, n1) == s[0] + sum(s.subrange(1, s.len() as int), (n1 - 1) as nat));
        assert(sum(s, n2) == s[0] + sum(s.subrange(1, s.len() as int), (n2 - 1) as nat));
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
fn below_zero(ops: Seq<int>) -> (result: bool)
    ensures result <==> exists|n: nat| n <= ops.len() && sum(ops, n) < 0
{
    let mut i: nat = 0;
    let mut current_sum: int = 0;
    while i < ops.len()
        invariant
            i <= ops.len(),
            current_sum == sum(ops, i),
            forall|k: nat| k <= i ==> sum(ops, k) >= 0
    {
        current_sum = current_sum + ops@[i as int];
        if current_sum < 0 {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

fn main() {
}

}