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
// <vc-helpers>
proof fn lemma_sum_succ_prefix(s: Seq<int>, n: nat)
    requires n < s.len()
    ensures sum(s, n + 1) == sum(s, n) + s@[n]
    decreases s.len() - n
{
    if n == 0 {
        // sum(s, 1) = s@[0] + sum(s.subrange(1, s.len()), 0) = s@[0] + 0
        assert(sum(s, 1) == s@[0] + sum(s.subrange(1, s.len() as int), 0));
        assert(sum(s, 0) == 0);
        assert(sum(s, 1) == sum(s, 0) + s@[0]);
    } else {
        // sum(s, n+1) = s@[0] + sum(s.subrange(1, ...), n)
        // sum(s, n)   = s@[0] + sum(s.subrange(1, ...), n-1)
        assert(sum(s, n + 1) == s@[0] + sum(s.subrange(1, s.len() as int), n));
        assert(sum(s, n) == s@[0] + sum(s.subrange(1, s.len() as int), n - 1));

        // apply induction on the subrange
        lemma_sum_succ_prefix(s.subrange(1, s.len() as int), n - 1);
        assert(sum(s.subrange(1, s.len() as int), n) ==
               sum(s.subrange(1, s.len() as int), n - 1) +
               s.subrange(1, s.len() as int)@[n - 1]);

        // subrange indexing shifts by 1
        assert(s.subrange(1, s.len() as int)@[n - 1] == s@[n]);

        // combine equalities
        assert(
            sum(s, n + 1) ==
            s@[0] + (sum(s.subrange(1, s.len() as int), n - 1) + s@[n])
        );
        assert(
            s@[0] + sum(s.subrange(1, s.len() as int), n - 1) ==
            sum(s, n)
        );
        assert(sum(s, n + 1) == sum(s, n) + s@[n]);
    }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn below_zero(ops: Seq<int>) -> (result: bool)
    ensures result <==> exists|n: nat| n <= ops.len() && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
{
    let mut i: nat = 0;
    let mut ssum: int = 0;
    while i < ops.len()
        invariant i <= ops.len()
        invariant ssum == sum(ops, i)
        invariant forall(|k: nat| k <= i ==> #[trigger] sum(ops, k) >= 0)
        decreases ops.len() - i
    {
        let v = ops@[i];
        let new = ssum + v;

        // relate new to sum(ops, i+1)
        lemma_sum_succ_prefix(ops, i);
        assert(sum(ops, i + 1) == new);

        if new < 0 {
            proof {
                // witness n = i+1
                assert(sum(ops, i + 1) == new);
                assert(sum(ops, i + 1) < 0);
                assert(exists(|n: nat| n <= ops.len() && sum(ops, n) < 0));
            }
            return true;
        }

        ssum = new;
        i = i + 1;

        proof {
            // maintain ssum == sum(ops, i)
            assert(ssum == sum(ops, i));

            // maintain forall k <= i, sum(ops,k) >= 0
            // For k < i it holds by previous invariant; for k == i it holds because new >= 0
            assert(forall(|k: nat| k <= i ==> sum(ops, k) >= 0));
        }
    }

    proof {
        // loop exited with i == ops.len() and forall k <= i sum(ops,k) >= 0,
        // so there is no n <= ops.len() with sum < 0
        assert(i == ops.len());
        assert(forall(|k: nat| k <= ops.len() ==> sum(ops, k) >= 0));
        assert(!exists(|n: nat| n <= ops.len() && sum(ops, n) < 0));
    }
    false
}
// </vc-code>

fn main() {
}

}