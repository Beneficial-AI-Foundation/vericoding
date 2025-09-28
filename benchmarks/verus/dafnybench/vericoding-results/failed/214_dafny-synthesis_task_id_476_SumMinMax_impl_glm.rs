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
proof fn min_seq_property(a: Seq<int>)
    requires
        a.len() > 0,
    ensures
        forall|i: int, j: int| 0 <= i < a.len() ==> 0 <= j < a.len() ==> min_seq(a) <= a[i],
        exists|i: int| 0 <= i < a.len() && min_seq(a) == a[i],
    decreases a.len()
{
    if a.len() == 1 {
        assert forall|i: int, j: int| 0 <= i < 1 ==> 0 <= j < 1 ==> a[0] <= a[i] by {
            assert(i == 0 && j == 0);
        }
        assert(0 <= 0 < 1 && min_seq(a) == a[0]);
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        assert(prefix.len() == a.len() - 1);
        assert(prefix.len() > 0);
        assert(prefix.len() < a.len());
        min_seq_property(prefix);

        let min_prefix = min_seq(prefix);
        assert forall|i: int| 0 <= i < prefix.len() ==> min_prefix <= prefix[i] by {
        }
        assert(exists|i: int| 0 <= i < prefix.len() && min_prefix == prefix[i]);

        let last = a[a.len() - 1];
        let min_a = min_seq(a);

        if last <= min_prefix {
            assert(min_a == last);
            assert forall|i: int, j: int| 0 <= i < a.len() ==> 0 <= j < a.len() ==> last <= a[i] by {
                if i < a.len() - 1 {
                    assert(a[i] == prefix[i]);
                    assert(last <= min_prefix);
                    assert(min_prefix <= prefix[i]);
                } else {
                    assert(i == a.len() - 1);
                }
            }
            assert(0 <= a.len() - 1 < a.len() && min_a == last);
        } else {
            assert(min_a == min_prefix);
            assert forall|i: int, j: int| 0 <= i < a.len() ==> 0 <= j < a.len() ==> min_prefix <= a[i] by {
                if i < a.len() - 1 {
                    assert(a[i] == prefix[i]);
                    assert(min_prefix <= prefix[i]);
                } else {
                    assert(i == a.len() - 1);
                    assert(last > min_prefix);
                }
            }
            assert(exists|i: int| 0 <= i < prefix.len() && min_prefix == prefix[i]);
            assert(0 <= i < a.len() && min_a == a[i]);
        }
    }
}

proof fn max_seq_property(a: Seq<int>)
    requires
        a.len() > 0,
    ensures
        forall|i: int, j: int| 0 <= i < a.len() ==> 0 <= j < a.len() ==> a[i] <= max_seq(a),
        exists|i: int| 0 <= i < a.len() && max_seq(a) == a[i],
    decreases a.len()
{
    if a.len() == 1 {
        assert forall|i: int, j: int| 0 <= i < 1 ==> 0 <= j < 1 ==> a[i] <= a[0] by {
            assert(i == 0 && j == 0);
        }
        assert(0 <= 0 < 1 && max_seq(a) == a[0]);
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        assert(prefix.len() == a.len() - 1);
        assert(prefix.len() > 0);
        assert(prefix.len() < a.len());
        max_seq_property(prefix);

        let max_prefix = max_seq(prefix);
        assert forall|i: int| 0 <= i < prefix.len() ==> prefix[i] <= max_prefix by {
        }
        assert(exists|i: int| 0 <= i < prefix.len() && max_prefix == prefix[i]);

        let last = a[a.len() - 1];
        let max_a = max_seq(a);

        if last >= max_prefix {
            assert(max_a == last);
            assert forall|i: int, j: int| 0 <= i < a.len() ==> 0 <= j < a.len() ==> a[i] <= last by {
                if i < a.len() - 1 {
                    assert(a[i] == prefix[i]);
                    assert(prefix[i] <= max_prefix);
                    assert(max_prefix <= last);
                } else {
                    assert(i == a.len() - 1);
                }
            }
            assert(0 <= a.len() - 1 < a.len() && max_a == last);
        } else {
            assert(max_a == max_prefix);
            assert forall|i: int, j: int| 0 <= i < a.len() ==> 0 <= j < a.len() ==> a[i] <= max_prefix by {
                if i < a.len() - 1 {
                    assert(a[i] == prefix[i]);
                    assert(prefix[i] <= max_prefix);
                } else {
                    assert(i == a.len() - 1);
                    assert(last < max_prefix);
                }
            }
            assert(exists|i: int| 0 <= i < prefix.len() && max_prefix == prefix[i]);
            assert(0 <= i < a.len() && max_a == a[i]);
        }
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
    let mut iter = a.iter();
    let mut min: i32 = *iter.next().unwrap();
    let mut max: i32 = min;
    let mut sum: i32 = min;

    proof {
        let a_seq = a@.map(|i: int, x: i32| x as int);
        min_seq_property(a_seq);
        max_seq_property(a_seq);
        assert(min_seq(a_seq) == min as int);
        assert(max_seq(a_seq) == max as int);
    }

    for x in iter
        invariant
            a.len() > 0,
            forall|i: int| #!auto 0 <= i < old(a).len() ==> old(a)[i] == a@[i],
            0 <= old(a).len() - a.len() < old(a).len(),
            min == min_seq(a@.map(|i: int, x: i32| x as int)) as i32,
            max == max_seq(a@.map(|i: int, x: i32| x as int)) as i32,
            sum + (a@[a.len()..].map(|i: int, x: i32| x as int)).sum::<int>() ==
            min_seq(old(a)@.map(|i: int, x: i32| x as int)) + max_seq(old(a)@.map(|i: int, x: i32| x as int))
    {
        if *x < min {
            min = *x;
        }
        if *x > max {
            max = *x;
        }
        sum += *x;

        proof {
            let old_a_seq = a@.map(|i: int, x: i32| x as int);
            let new_a_seq = old_a_seq.take_last();
            assert(a@ == new_a_seq.push(*x as int));

            let old_min = min_seq(old_a_seq);
            let old_max = max_seq(old_a_seq);
            let new_min = min_seq(new_a_seq);
            let new_max = max_seq(new_a_seq);

            if *x as int <= new_min {
                assert(old_min == *x as int);
            } else {
                assert(old_min == new_min);
            }

            if *x as int >= new_max {
                assert(old_max == *x as int);
            } else {
                assert(old_max == new_max);
            }

            assert(old_min + old_max == sum as int);
        }
    }

    proof {
        assert(a.len() == 0);
    }

    sum
}
// </vc-code>

fn main() {}

}