use vstd::prelude::*;

verus! {

// Given an array of integers, it returns the sum. [1,3,3,2]->9

spec fn sum(xs: Seq<i32>) -> int
    decreases xs.len()
{
    if xs.len() == 0 {
        0int
    } else {
        sum(xs.subrange(0, xs.len() - 1)) + xs[xs.len() - 1] as int
    }
}

// <vc-helpers>
proof fn sum_subrange_last(s: Seq<i32>, k: nat)
    requires k < s.len()
    ensures sum(s.subrange(0, k+1)) == sum(s.subrange(0, k)) + s@[k] as int
{
    let t = s.subrange(0, k + 1);
    // t.len() == k+1 > 0
    assert(t.len() == k + 1);
    reveal(sum);
    // By definition of sum on non-empty sequence t:
    // sum(t) == sum(t.subrange(0, t.len() - 1)) + t@[t.len() - 1] as int
    assert(sum(t) == sum(t.subrange(0, t.len() - 1)) + t@[t.len() - 1] as int);
    // t.len() - 1 == k
    assert(t.len() - 1 == k);
    // t@[t.len()-1] == s@[k] and t.subrange(0, t.len()-1) == s.subrange(0, k)
    assert(t@[t.len() - 1] == s@[k]);
    assert(t.subrange(0, t.len() - 1) == s.subrange(0, k));
    // Combine equalities to conclude the goal
    assert(sum(s.subrange(0, k + 1)) == sum(s.subrange(0, k)) + s@[k] as int);
}
// </vc-helpers>

// <vc-spec>
fn sum_array(xs: &[i32]) -> (s: i32)
    ensures s as int == sum(xs@)
// </vc-spec>
// <vc-code>
{
    let n = xs.len();
    proof {
        assert(n as nat == xs@.len());
    }
    let mut i: usize = 0;
    let mut acc: i32 = 0;
    while i < n
        invariant i <= n
        invariant (acc as int) == sum(xs@.subrange(0, (i as nat)))
        decreases (n - i)
    {
        let old_acc = acc;
        let v = xs[i];
        acc = old_acc + v;
        proof {
            // i < n holds due to loop condition, show as nat for lemma
            assert(i < n);
            assert(n as nat == xs@.len());
            assert((i as nat) < xs@.len());
            sum_subrange_last(xs@, i as nat);
        }
        assert((acc as int) == sum(xs@.subrange(0, ((i + 1) as nat))));
        i += 1;
    }
    proof {
        // When loop exits, i == n, so acc equals sum of full sequence
        assert(i == n);
        assert(n as nat == xs@.len());
        assert(xs@.subrange(0, (n as nat)) == xs@);
        assert((acc as int) == sum(xs@.subrange(0, (n as nat))));
        assert((acc as int) == sum(xs@));
    }
    acc
}
// </vc-code>

fn main() {
}

}