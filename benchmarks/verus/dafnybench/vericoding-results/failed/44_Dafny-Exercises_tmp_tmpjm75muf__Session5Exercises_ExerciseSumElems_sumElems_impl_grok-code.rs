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
#[verifier::proof]
fn sum_r_commutative(s: Seq<int>)
    ensures
        sum_r(s) == sum_l(s),
    decreases s.len()
{
    if s.len() == 0 {
        assert(sum_r(s) == 0);
        assert(sum_l(s) == 0);
    } else {
        sum_r_commutative(s.subrange(0, s.len() - 1));
        sum_r_commutative(s.subrange(1, s.len()));
        assert(sum_r(s) == sum_r(s.subrange(0, s.len() - 1)) + s[s.len() - 1]);
        assert(sum_l(s) == s[0] + sum_l(s.subrange(1, s.len())));
        assert(sum_r(s.subrange(0, s.len() - 1)) == sum_l(s.subrange(0, s.len() - 1)));
        assert(sum_l(s.subrange(1, s.len())) == sum_r(s.subrange(1, s.len())));
        assert(sum_l(s) == sum_r(s));
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
    let s: Ghost<Seq<int>> = Ghost(v@.map(|i: int, x: i32| x as int));
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    let len: usize = v.len();
    while i < len
        invariant
            i <= len,
            sum as int == sum_r(s@.subrange(0, i as int))
    {
        sum = sum.checked_add(v[i]).unwrap();
        i += 1;
        proof {
            let prefix_prev = s@.subrange(0, (i as int - 1));
            assert(sum as int == sum_r(prefix_prev) + s@[(i as int - 1)]);
            assert(sum_r(s@.subrange(0, i as int)) == sum_r(prefix_prev.add(seq![s@[(i as int - 1)]])) == sum_r(prefix_prev) + s@[(i as int - 1)]);
        }
    }
    sum
}
// </vc-code>

fn main() {}

}