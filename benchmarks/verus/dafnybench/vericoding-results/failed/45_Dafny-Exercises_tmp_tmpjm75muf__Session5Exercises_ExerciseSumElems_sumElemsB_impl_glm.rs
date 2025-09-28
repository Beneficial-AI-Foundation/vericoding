use vstd::prelude::*;

verus! {

spec fn sum_r(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        sum_r(s.subrange(0, s.len() - 1)) + s[s.len() - 1]
    }
}

spec fn sum_l(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum_l(s.subrange(1, s.len() as int))
    }
}


spec fn sum_v(v: Seq<int>, c: int, f: int) -> int
{
    if 0 <= c <= f <= v.len() {
        sum_r(v.subrange(c, f))
    } else {
        0
    }
}

// <vc-helpers>
proof fn lemma_sum_r_subrange(s: Seq<int>, i: int)
    requires 0 <= i <= s.len()
    ensures sum_r(s) == sum_r(s.subrange(0, i)) + sum_r(s.subrange(i, s.len()))
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.subrange(0, i) == Seq::empty());
        assert(s.subrange(i, s.len()) == Seq::empty());
        assert(sum_r(s) == 0);
        assert(sum_r(s.subrange(0, i)) + sum_r(s.subrange(i, s.len())) == 0 + 0);
    } else {
        let n = s.len();
        if i == n {
            assert(s.subrange(0, i) == s);
            assert(s.subrange(i, s.len()) == Seq::empty());
            assert(sum_r(s) == sum_r(s) + 0);
        } else {
            lemma_sum_r_subrange(s.subrange(0, n - 1), i);
            assert(sum_r(s) == sum_r(s.subrange(0, n - 1)) + s[n - 1]);
            assert(sum_r(s.subrange(0, n - 1)) == sum_r(s.subrange(0, i)) + sum_r(s.subrange(i, n - 1)));
            assert(s.subrange(i, n) == s.subrange(i, n - 1).push(s[n - 1]));
            assert(sum_r(s.subrange(i, n)) == sum_r(s.subrange(i, n - 1)) + s[n - 1]);
            assert(sum_r(s) == sum_r(s.subrange(0, i)) + sum_r(s.subrange(i, n)));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_elems_b(v: &[i32]) -> (sum: i32)
//ensures sum as int == sum_l(v@.map(|i, x| x as int))
ensures sum as int == sum_r(v@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    let mut i = 0;
    let mut sum = 0;
    let n = v.len();

    while i < n
        invariant {
            0 <= i <= n,
            sum as int == sum_r(v@.subrange(0, i).map(|i, x| x as int)),
        }
    {
        sum = sum + v[i];
        i = i + 1;
    }

    sum
}
// </vc-code>

fn main() {
}

}