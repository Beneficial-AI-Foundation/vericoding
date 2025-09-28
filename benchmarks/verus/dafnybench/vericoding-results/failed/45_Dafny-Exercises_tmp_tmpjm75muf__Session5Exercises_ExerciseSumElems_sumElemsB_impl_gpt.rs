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
proof fn sum_r_prefix_extend(s: Seq<int>, k: int)
    requires
        0 <= k < s.len()
    ensures
        sum_r(s.subrange(0, k + 1)) == sum_r(s.subrange(0, k)) + s[k]
{
    reveal_with_fuel(sum_r, 2);
    assert(s.subrange(0, k + 1).len() == k + 1) by {
        assert(k + 1 <= s.len());
    }
    assert(sum_r(s.subrange(0, k + 1))
        == sum_r(s.subrange(0, k + 1).subrange(0, (k + 1) - 1))
            + s.subrange(0, k + 1)[(k + 1) - 1]);
    assert((k + 1) - 1 == k);
    assert(s.subrange(0, k + 1).subrange(0, k) == s.subrange(0, k));
}
// </vc-helpers>

// <vc-spec>
fn sum_elems_b(v: &[i32]) -> (sum: i32)
//ensures sum as int == sum_l(v@.map(|i, x| x as int))
ensures sum as int == sum_r(v@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    let n = v.len();
    let mut i: usize = 0;
    let mut acc: i32 = 0;

    while i < n
        invariant
            i <= n,
            n == v.len(),
            0 <= i as int <= v@.len(),
            acc as int == sum_r(v@.map(|j, x| x as int).subrange(0, i as int))
        decreases n - i
    {
        let x = v[i];
        proof {
            let s = v@.map(|j, y| y as int);
            let k: int = i as int;
            assert(s.len() == v@.len());
            assert(0 <= k < s.len());
            sum_r_prefix_extend(s, k);
            assert(s[k] == v@[k] as int);
            assert((acc + x) as int == acc as int + x as int);
            assert(
                (acc + x) as int
                == sum_r(s.subrange(0, k)) + s[k]
            );
            assert(
                (acc + x) as int
                == sum_r(s.subrange(0, k + 1))
            );
        }
        i = i + 1;
        acc = acc + x;
        proof {
            let s2 = v@.map(|j, y| y as int);
            let k2: int = i as int;
            assert(k2 == (i as int));
            assert(k2 > 0);
            assert(s2.len() == v@.len());
            assert(k2 <= s2.len());
            assert(acc as int == sum_r(s2.subrange(0, k2)));
        }
    }

    proof {
        let s = v@.map(|j, x| x as int);
        assert(i == n);
        assert(i as int == s.len());
        assert(s.subrange(0, s.len()) == s);
        assert(acc as int == sum_r(s));
    }

    acc
}
// </vc-code>

fn main() {
}

}