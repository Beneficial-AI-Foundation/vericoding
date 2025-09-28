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
proof fn sum_nonnegative(s: Seq<int>, n: nat)
    requires
        n <= s.len(),
        forall|i: int| 0 <= i && i < n ==> s[i] >= 0,
    ensures
        sum(s, n) >= 0,
    decreases n
{
    if n == 0 {
    } else {
        assert(s[0] >= 0);
        sum_nonnegative(s.subrange(1, s.len() as int), (n - 1) as nat);
    }
}

spec fn prefix_sum_nonnegative(s: Seq<int>, n: nat) -> bool
    recommends n <= s.len()
{
    forall|i: int| 0 <= i && i < n ==> s[i] >= 0
}

spec fn has_negative_prefix(s: Seq<int>) -> bool
    decreases s.len()
{
    if s.len() == 0 {
        false
    } else {
        s[0] < 0 || has_negative_prefix(s.subrange(1, s.len() as int))
    }
}

proof fn sum_negative_implies_has_negative_prefix(s: Seq<int>, n: nat)
    requires
        n <= s.len(),
        sum(s, n) < 0,
    ensures
        has_negative_prefix(s),
    decreases n
{
    if n == 0 {
    } else {
        if s[0] < 0 {
        } else {
            sum_negative_implies_has_negative_prefix(s.subrange(1, s.len() as int), (n - 1) as nat);
        }
    }
}

proof fn has_negative_prefix_implies_sum_negative(s: Seq<int>)
    requires
        has_negative_prefix(s),
    ensures
        exists|n: nat| n <= s.len() && sum(s, n) < 0,
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        if s[0] < 0 {
            assert(sum(s, 1) == s[0]);
        } else {
            has_negative_prefix_implies_sum_negative(s.subrange(1, s.len() as int));
        }
    }
}

proof fn seq_index_agreement<T>(s: Seq<T>, j: usize)
    ensures
        s@.index(j) == s[j as int]
{
}
// </vc-helpers>

// <vc-spec>
fn below_zero(ops: Seq<int>) -> (result: bool)
    ensures result <==> exists|n: nat| n <= ops.len() && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
{
    let mut total: int = 0;
    let mut i: usize = 0;
    while i < ops.len() as usize
        invariant
            i <= ops.len(),
            total == sum(ops, i as nat),
    {
        if total < 0 {
            return true;
        }
        proof {
            seq_index_agreement(ops, i);
        }
        total = total + ops[i];
        i = i + 1;
    }
    false
}
// </vc-code>

fn main() {
}

}