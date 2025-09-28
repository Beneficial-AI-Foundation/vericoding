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
spec fn sum_range_int_seq(s: Seq<int>, start: int, end: int) -> int {
    if start >= end {
        0
    } else {
        sum_range_int_seq(s, start, end - 1) + s[end - 1]
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
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            sum as int == sum_range_int_seq(v@.map(|k, x| x as int), 0, i as int),
            sum as int == sum_r(v@.map(|k, x| x as int).subrange(0, i as int)),
        decreases (v.len() - i) as int
    {
        sum = sum + v[i];
        i = i + 1;
    }
    sum
}
// </vc-code>

fn main() {}

}