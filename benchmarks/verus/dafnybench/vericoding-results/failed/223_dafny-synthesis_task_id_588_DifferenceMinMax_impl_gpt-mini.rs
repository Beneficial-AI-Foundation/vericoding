use vstd::prelude::*;

verus! {

// The order of the recursion in these two functions
// must match the order of the iteration in the algorithm above
spec fn min(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.take(a.len() - 1);
        let min_prefix = min(prefix);
        if a[a.len() - 1] <= min_prefix {
            a[a.len() - 1]
        } else {
            min_prefix
        }
    }
}

spec fn max(a: Seq<int>) -> int
    recommends a.len() > 0  
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.take(a.len() - 1);
        let max_prefix = max(prefix);
        if a[a.len() - 1] >= max_prefix {
            a[a.len() - 1]
        } else {
            max_prefix
        }
    }
}

// <vc-helpers>
proof fn min_take_succ(s: Seq<int>, i: nat)
    requires 1 <= i && i < s.len()
    ensures min(s.take(i+1)) == if s@[i] <= min(s.take(i)) { s@[i] } else { min(s.take(i)) }
    decreases s.len() - i
{
    let t = s.take(i+1);
    assert(t.len() == i+1);
    // Unfold definition of min on t
    assert(min(t) == if t.len() == 1 { t@[0] } else {
        let prefix = t.take(t.len() - 1);
        let mp = min(prefix);
        let last = t@[t.len() - 1];
        if last <= mp { last } else { mp }
    });
    // Since i >= 1, t.len() = i+1 >= 2, so use the else case
    let prefix = t.take(t.len() - 1);
    assert(prefix == s.take(i));
    let last = t@[t.len() - 1];
    assert(last == s@[i]);
    assert(min(t) == if s@[i] <= min(s.take(i)) { s@[i] } else { min(s.take(i)) });
}

proof fn max_take_succ(s: Seq<int>, i: nat)
    requires 1 <= i && i < s.len()
    ensures max(s.take(i+1)) == if s@[i] >= max(s.take(i)) { s@[i] } else { max(s.take(i)) }
    decreases s.len() - i
{
    let t = s.take(i+1);
    assert(t.len() == i+1);
    // Unfold definition of max on t
    assert(max(t) == if t.len() == 1 { t@[0] } else {
        let prefix = t.take(t.len() - 1);
        let mp = max(prefix);
        let last = t@[t.len() - 1];
        if last >= mp { last } else { mp }
    });
    // Since i >= 1, t.len() = i+1 >= 2, so use the else case
    let prefix = t.take(t.len() - 1);
    assert(prefix == s.take(i));
    let last = t@[t.len() - 1];
    assert(last == s@[i]);
    assert(max(t) == if s@[i] >= max(s.take(i)) { s@[i] } else { max(s.take(i)) });
}
// </vc-helpers>

// <vc-spec>
fn difference_min_max(a: &[i32]) -> (diff: i32)
    requires a.len() > 0
    ensures diff == max(a@.map(|i, x| x as int)) - min(a@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    let s: Seq<int> = a@.map(|_, x: i32| x as int);
    // initialize with first element
    let mut i: usize = 1;
    let mut cur_min: i32 = a[0];
    let mut cur_max: i32 = a[0];

    // Loop over remaining elements, maintaining that cur_min/cur_max
    // are the min/max of the prefix s.take(i), with 1 <= i <= a.len()
    while i < a.len()
        invariant { 1 <= i && i <= a.len() }
        invariant { (cur_min as int) == min(s.take(i)) }
        invariant { (cur_max as int) == max(s.take(i)) }
        decreases a.len() - i
    {
        let x: i32 = a[i];
        // Save old values for proofs
        let old_min: i32 = cur_min;
        let old_max: i32 = cur_max;

        // Update min/max in the usual way
        if x < cur_min {
            cur_min = x;
        }
        if x > cur_max {
            cur_max = x;
        }

        // Proof that invariants hold for i+1
        proof {
            // Relate Rust values to spec sequence values
            assert((old_min as int) == min(s.take(i)));
            assert((old_max as int) == max(s.take(i)));
            assert((x as int) == s@[i]);

            // Apply lemmas about taking one more element
            min_take_succ(s, i);
            max_take_succ(s, i);

            // Show cur_min corresponds to min(s.take(i+1))
            if x < old_min {
                // cur_min was set to x, which equals s@[i]
                assert(cur_min as int == s@[i]);
                // x < old_min implies (x as int) < min(s.take(i)), hence <= also holds
                assert((x as int) < min(s.take(i)));
                assert(s@[i] <= min(s.take(i)));
                // By lemma, min(s.take(i+1)) == s@[i]
                assert(min(s.take(i+1)) == s@[i]);
                assert(cur_min as int == min(s.take(i+1)));
            } else {
                // cur_min unchanged == old_min == min(s.take(i))
                assert(cur_min as int == min(s.take(i)));
                if s@[i] <= min(s.take(i)) {
                    // From !(x < old_min) we know (x as int) >= min(s.take(i)), so combined gives equality
                    assert((x as int) >= min(s.take(i)));
                    assert(s@[i] == min(s.take(i)));
                    assert(min(s.take(i+1)) == min(s.take(i)));
                } else {
                    // s@[i] > min(prefix) -> lemma gives min(s.take(i+1)) == min(prefix)
                    assert(min(s.take(i+1)) == min(s.take(i)));
                }
                assert(cur_min as int == min(s.take(i+1)));
            }

            // Show cur_max corresponds to max(s.take(i+1))
            if x > old_max {
                // cur_max was set to x, which equals s@[i]
                assert(cur_max as int == s@[i]);
                assert((x as int) > max(s.take(i)));
                assert(max(s.take(i+1)) == s@[i]);
                assert(cur_max as int == max(s.take(i+1)));
            } else {
                // cur_max unchanged == old_max == max(s.take(i))
                assert(cur_max as int == max(s.take(i)));
                if s@[i] >= max(s.take(i)) {
                    // From !(x > old_max) we know (x as int) <= max(s.take(i)), so combined gives equality
                    assert((x as int) <= max(s.take(i)));
                    assert(s@[i] == max(s.take(i)));
                    assert(max(s.take(i+1)) == max(s.take(i)));
                } else {
                    // s@[i] < max(prefix) -> lemma gives max(s.take(i+1)) == max(prefix)
                    assert(max(s.take(i+1)) == max(s.take(i)));
                }
                assert(cur_max as int == max(s.take(i+1)));
            }
        }

        i += 1;
    }

    // At this point i == a.len(), so cur_min/cur_max are min/max of whole sequence
    proof {
        assert(i == a.len());
        assert((cur_min as int) == min(s.take(a.len())));
        assert((cur_max as int) == max(s.take(a.len())));
        // s.take(a.len()) == s, so we have:
        assert((cur_min as int) == min(s));
        assert((cur_max as int) == max(s));
    }

    let diff_int: int = (cur_max as int) - (cur_min as int);
    let diff_i32: i32 = diff_int as i32;
    diff_i32
}
// </vc-code>

fn main() {}

}