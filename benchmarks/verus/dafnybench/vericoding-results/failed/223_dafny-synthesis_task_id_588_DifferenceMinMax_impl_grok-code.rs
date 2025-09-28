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
proof fn min_additional_properties(a: Seq<int>)
    requires a.len() > 0
    ensures forall|i: int| 0 <= i < a.len() ==> min(a) <= a[i]
    decreases a.len()
{
    if a.len() == 1 {
        // trivial
    } else {
        let prefix = a.take(a.len() - 1);
        let min_prefix = min(prefix);
        min_additional_properties(prefix);
        let last = a.len() - 1;
        if a[last] <= min_prefix {
            assert(min(a) == a[last]);
            assert forall|i: int| 0 <= i < a.len() ==> min(a) <= a[i] by {
                if i < last {
                    // prefix[i], and from inductive, min_prefix <= a[i], so a[last] <= min_prefix <= a[i]
                    assert(min_prefix <= a[i]);
                } else {
                    // i == last
                    assert(a[last] <= a[last]);
                }
            }
        } else {
            assert(min(a) == min_prefix);
            assert(min_prefix <= a[last]);
            // and from inductive, min_prefix <= a[i] for all i < last, and min_prefix <= a[last], so for all i
            assert forall|i: int| 0 <= i < a.len() ==> min(a) <= a[i] by {
                assert(min_prefix <= a[i]);
            }
        }
    }
}

proof fn max_additional_properties(a: Seq<int>)
    requires a.len() > 0
    ensures forall|i: int| 0 <= i < a.len() ==> a[i] <= max(a)
    decreases a.len()
{
    if a.len() == 1 {
        // trivial
    } else {
        let prefix = a.take(a.len() - 1);
        let max_prefix = max(prefix);
        max_additional_properties(prefix);
        let last = a.len() - 1;
        if a[last] >= max_prefix {
            assert(max(a) == a[last]);
            assert forall|i: int| 0 <= i < a.len() ==> a[i] <= max(a) by {
                if i < last {
                    // from inductive, a[i] <= max_prefix, and max_prefix <= a[last], so a[i] <= a[last]
                    assert(a[i] <= max_prefix);
                } else {
                    assert(a[last] <= max(a));
                }
            }
        } else {
            assert(max(a) == max_prefix);
            assert(a[last] <= max_prefix);
            assert forall|i: int| 0 <= i < a.len() ==> a[i] <= max(a) by {
                if i < last {
                    // from inductive, a[i] <= max_prefix
                    assert(a[i] <= max_prefix);
                } else {
                    assert(a[last] <= max_prefix);
                }
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn difference_min_max(a: &[i32]) -> (diff: i32)
    requires a.len() > 0
    ensures diff == max(a@.map(|i, x| x as int)) - min(a@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    let ghost a_seq = a@.map(|i, x| x as int);

    assert(a_seq.len() > 0);

    proof {
        min_additional_properties(a_seq);
        max_additional_properties(a_seq);
    }

    let mut min_val = a[0];
    let mut max_val = a[0];

    assert(min_val as int == min(a_seq.take(1))) by {
        let i: int = 0;
        assert(0 <= i < a_seq.len());
        assert(min(a_seq.take(1)) <= a_seq[i]);
        assert(a_seq[i] <= max(a_seq.take(1)));
        assert(min(a_seq.take(1)) == a_seq[i]);
        assert(a_seq[i] == a[0] as int);
    }

    let mut i = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            a_seq.take(i as int).len() > 0,
            forall|j: int| 0 <= j < i ==> min_val <= a[j],
            min_val as int == min(a_seq.take(i as int)),
            forall|j: int| 0 <= j < i ==> a[j] <= max_val,
            a_seq.take(i as int).len() > 0,
            max_val as int == max(a_seq.take(i as int)),
        decreases a.len() - i
    {
        if a[i] < min_val {
            min_val = a[i];
        }
        if a[i] > max_val {
            max_val = a[i];
        }
        i += 1;
    }

    assert(min_val as int == min(a_seq));
    assert(max_val as int == max(a_seq));

    (max_val - min_val)
}
// </vc-code>

fn main() {}

}