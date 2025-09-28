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
proof fn lemma_min_unfold(s: Seq<int>)
    requires s.len() > 1
    ensures
        min_seq(s)
        ==
        {
            let pre = s.subrange(0, s.len() - 1);
            if s[s.len() - 1] <= min_seq(pre) {
                s[s.len() - 1]
            } else {
                min_seq(pre)
            }
        }
{
    let pre = s.subrange(0, s.len() - 1);
    assert(s.len() > 1);
    assert(
        min_seq(s)
        ==
        if s[s.len() - 1] <= min_seq(pre) {
            s[s.len() - 1]
        } else {
            min_seq(pre)
        }
    );
}

proof fn lemma_max_unfold(s: Seq<int>)
    requires s.len() > 1
    ensures
        max_seq(s)
        ==
        {
            let pre = s.subrange(0, s.len() - 1);
            if s[s.len() - 1] >= max_seq(pre) {
                s[s.len() - 1]
            } else {
                max_seq(pre)
            }
        }
{
    let pre = s.subrange(0, s.len() - 1);
    assert(s.len() > 1);
    assert(
        max_seq(s)
        ==
        if s[s.len() - 1] >= max_seq(pre) {
            s[s.len() - 1]
        } else {
            max_seq(pre)
        }
    );
}

proof fn lemma_min_base(s: Seq<int>)
    requires s.len() == 1
    ensures min_seq(s) == s[0]
{
    assert(min_seq(s) == s[0]);
}

proof fn lemma_max_base(s: Seq<int>)
    requires s.len() == 1
    ensures max_seq(s) == s[0]
{
    assert(max_seq(s) == s[0]);
}
// </vc-helpers>

// <vc-spec>
fn sum_min_max(a: &[i32]) -> (sum: i32)
    requires a.len() > 0
    ensures sum == max_seq(a@.map(|i: int, x: i32| x as int)) + min_seq(a@.map(|i: int, x: i32| x as int))
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut min = a[0];
    let mut max = a[0];

    proof {
        let s = a@.map(|j: int, x: i32| x as int);
        assert(n > 0);
        assert(s.len() == n as int);
        let pre = s.subrange(0, 1);
        assert(pre.len() == 1);
        lemma_min_base(pre);
        lemma_max_base(pre);
        assert(pre[0] == s[0]);
        assert(min as int == s[0]);
        assert(max as int == s[0]);
        assert(min as int == min_seq(pre));
        assert(max as int == max_seq(pre));
    }

    let mut i: usize = 1;
    while i < n
        invariant
            1 <= i as int <= n as int,
            min as int == min_seq(a@.map(|j: int, x: i32| x as int).subrange(0, i as int)),
            max as int == max_seq(a@.map(|j: int, x: i32| x as int).subrange(0, i as int)),
            a.len() == n
    {
        let x = a[i];
        let old_min = min;
        let old_max = max;

        if x < min {
            min = x;
        }
        if x > max {
            max = x;
        }

        proof {
            let s = a@.map(|j: int, y: i32| y as int);
            let pre = s.subrange(0, i as int);
            let ext = s.subrange(0, i as int + 1);

            assert(s.len() == n as int);
            assert(i as int < s.len());
            assert(ext.len() == i as int + 1);
            assert(ext.len() > 1);

            assert(s[i as int] == (a@[i as int]) as int);
            assert(a@[i as int] == x);

            // Unfold recursive specs on ext
            lemma_min_unfold(ext);
            lemma_max_unfold(ext);

            // Update for min
            if x < old_min {
                assert((x as int) <= (old_min as int));
                assert(min as int == x as int);
                assert(min_seq(ext) == if s[i as int] <= min_seq(pre) { s[i as int] } else { min_seq(pre) });
                assert(min_seq(pre) == old_min as int);
                assert(s[i as int] == x as int);
                assert(min as int == min_seq(ext));
            } else {
                // x >= old_min
                assert((x as int) >= (old_min as int));
                assert(min as int == old_min as int);
                assert(min_seq(ext) == if s[i as int] <= min_seq(pre) { s[i as int] } else { min_seq(pre) });
                assert(min_seq(pre) == old_min as int);
                assert(s[i as int] == x as int);
                if s[i as int] <= min_seq(pre) {
                    assert((x as int) <= (old_min as int));
                    assert((x as int) >= (old_min as int));
                    assert((x as int) == (old_min as int));
                    assert(s[i as int] == min_seq(pre));
                    assert(min_seq(ext) == min_seq(pre));
                } else {
                    assert(min_seq(ext) == min_seq(pre));
                }
                assert(min_seq(ext) == old_min as int);
                assert(min as int == min_seq(ext));
            }

            // Update for max
            if x > old_max {
                assert((x as int) >= (old_max as int));
                assert(max as int == x as int);
                assert(max_seq(ext) == if s[i as int] >= max_seq(pre) { s[i as int] } else { max_seq(pre) });
                assert(max_seq(pre) == old_max as int);
                assert(s[i as int] == x as int);
                assert(max as int == max_seq(ext));
            } else {
                // x <= old_max
                assert((x as int) <= (old_max as int));
                assert(max as int == old_max as int);
                assert(max_seq(ext) == if s[i as int] >= max_seq(pre) { s[i as int] } else { max_seq(pre) });
                assert(max_seq(pre) == old_max as int);
                assert(s[i as int] == x as int);
                if s[i as int] >= max_seq(pre) {
                    assert((x as int) >= (old_max as int));
                    assert((x as int) <= (old_max as int));
                    assert((x as int) == (old_max as int));
                    assert(s[i as int] == max_seq(pre));
                    assert(max_seq(ext) == max_seq(pre));
                } else {
                    assert(max_seq(ext) == max_seq(pre));
                }
                assert(max_seq(ext) == old_max as int);
                assert(max as int == max_seq(ext));
            }
        }

        i = i + 1;
    }

    proof {
        let s = a@.map(|j: int, x: i32| x as int);
        assert(i == n);
        assert(min as int == min_seq(s.subrange(0, n as int)));
        assert(max as int == max_seq(s.subrange(0, n as int)));
        assert(s.len() == n as int);
        assert(s.subrange(0, s.len()) == s);
        assert(s.subrange(0, n as int) == s);
    }

    let sum = min + max;
    sum
}
// </vc-code>

fn main() {}

}