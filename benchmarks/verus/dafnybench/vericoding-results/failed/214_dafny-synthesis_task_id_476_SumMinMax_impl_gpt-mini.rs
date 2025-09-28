use vstd::prelude::*;

verus! {

// The order of the recursion in these two functions
// must match the order of the iteration in the algorithm above
spec fn min_seq(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        assume(prefix.len() < a.len());
        let min_prefix = min_seq(prefix);
        if a[a.len() - 1] <= min_prefix {
            a[a.len() - 1]
        } else {
            min_prefix
        }
    }
}

spec fn max_seq(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        assume(prefix.len() < a.len());
        let max_prefix = max_seq(prefix);
        if a[a.len() - 1] >= max_prefix {
            a[a.len() - 1]
        } else {
            max_prefix
        }
    }
}

// <vc-helpers>
proof fn min_seq_len1(s: Seq<int>)
    requires s.len() >= 1
    ensures min_seq(s.subrange(0,1)) == s@[0]
{
    // By definition of min_seq on length 1
}

proof fn min_seq_subrange_last(s: Seq<int>, k: nat)
    requires 2 <= k && k <= s.len()
    ensures min_seq(s.subrange(0,k)) == if s@[k-1] <= min_seq(s.subrange(0,k-1)) { s@[k-1] } else { min_seq(s.subrange(0,k-1)) }
    decreases k
{
    if k == 2 {
        min_seq_len1(s.subrange(0,1));
    } else {
        min_seq_subrange_last(s, k - 1);
    }
}

proof fn max_seq_len1(s: Seq<int>)
    requires s.len() >= 1
    ensures max_seq(s.subrange(0,1)) == s@[0]
{
    // By definition of max_seq on length 1
}

proof fn max_seq_subrange_last(s: Seq<int>, k: nat)
    requires 2 <= k && k <= s.len()
    ensures max_seq(s.subrange(0,k)) == if s@[k-1] >= max_seq(s.subrange(0,k-1)) { s@[k-1] } else { max_seq(s.subrange(0,k-1)) }
    decreases k
{
    if k == 2 {
        max_seq_len1(s.subrange(0,1));
    } else {
        max_seq_subrange_last(s, k - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_min_max(a: &[i32]) -> (sum: i32)
    requires a.len() > 0
    ensures sum == max_seq(a@.map(|i: int, x: i32| x as int)) + min_seq(a@.map(|i: int, x: i32| x as int))
// </vc-spec>
// <vc-code>
{
    let s = a@.map(|i: int, x: i32| x as int);
    let n: nat = s.len();

    // initialize with first element
    let mut i: nat = 1;
    let mut cur_min: int = a[0] as int;
    let mut cur_max: int = a[0] as int;

    // prove initial equalities for invariants
    proof {
        min_seq_len1(s.subrange(0,1));
        assert(cur_min == min_seq(s.subrange(0,1)));
        max_seq_len1(s.subrange(0,1));
        assert(cur_max == max_seq(s.subrange(0,1)));
    }

    while i < n
        invariant 1 <= i && i <= n;
        invariant cur_min == min_seq(s.subrange(0, i));
        invariant cur_max == max_seq(s.subrange(0, i));
        decreases n - i;
    {
        let v: int = a[i as usize] as int;

        let new_min: int = if v <= cur_min { v } else { cur_min };
        let new_max: int = if v >= cur_max { v } else { cur_max };

        // prove the invariants hold after incorporating a[i]
        proof {
            min_seq_subrange_last(s, i + 1);
            assert(v == s@[i]);
            assert(cur_min == min_seq(s.subrange(0, i)));
            if v <= cur_min {
                assert(new_min == s@[i]);
                assert(new_min == min_seq(s.subrange(0, i + 1)));
            } else {
                assert(new_min == cur_min);
                assert(new_min == min_seq(s.subrange(0, i + 1)));
            }

            max_seq_subrange_last(s, i + 1);
            assert(cur_max == max_seq(s.subrange(0, i)));
            if v >= cur_max {
                assert(new_max == s@[i]);
                assert(new_max == max_seq(s.subrange(0, i + 1)));
            } else {
                assert(new_max == cur_max);
                assert(new_max == max_seq(s.subrange(0, i + 1)));
            }
        }

        cur_min = new_min;
        cur_max = new_max;
        i = i + 1;
    }

    cur_min + cur_max
}
// </vc-code>

fn main() {}

}