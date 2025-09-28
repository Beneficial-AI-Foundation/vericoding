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

spec fn sum_v(v: Seq<int>, c: int, f: int) -> int {
    if 0 <= c <= f <= v.len() {
        sum_r(v.subrange(c, f))
    } else {
        0
    }
}

// <vc-helpers>
proof fn lemma_sum_r_equals_sum_l(s: Seq<int>)
    decreases s.len()
    ensures sum_r(s) == sum_l(s)
{
    if s.len() == 0 {
    } else if s.len() == 1 {
        assert(sum_r(s) == s[0]);
        assert(sum_l(s) == s[0]);
    } else {
        let n = s.len();
        let first = s[0];
        let last = s[n-1];
        let mid = s.subrange(1, n-1);

        lemma_sum_r_equals_sum_l(s.subrange(0, n-1));
        lemma_sum_r_equals_sum_l(s.subrange(1, n));
        lemma_sum_r_equals_sum_l(mid);

        assert(sum_r(s) == sum_r(s.subrange(0, n-1)) + last);
        assert(sum_r(s.subrange(0, n-1)) == sum_l(s.subrange(0, n-1)));
        assert(sum_l(s.subrange(0, n-1)) == first + sum_l(mid));
        assert(sum_l(s) == first + sum_l(s.subrange(1, n)));
        assert(sum_l(s.subrange(1, n)) == sum_r(s.subrange(1, n)));
        assert(sum_r(s.subrange(1, n)) == sum_r(mid) + last);
        assert(sum_l(mid) == sum_r(mid));
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_elems(v: &[i32]) -> (sum: i32)
//ensures sum as int == sum_l(v@.map(|i, x| x as int))
ensures sum as int == sum_r(v@.map(|i, x| x as int))
//ensures sum as int == sum_v(v@.map(|i, x| x as int), 0, v@.len())
// </vc-spec>
// <vc-code>
{
    let mut total: i32 = 0;
    let mut i: usize = 0;
    let n = v.len();
    let v_seq = v@.map(|i, x| x as int);
    while i < n
        invariant 0 <= i <= n
        invariant total as int == sum_r(v_seq.subrange(0, i))
    {
        total = total + v[i];
        i = i + 1;
    }
    total
}
// </vc-code>

fn main() {}

}