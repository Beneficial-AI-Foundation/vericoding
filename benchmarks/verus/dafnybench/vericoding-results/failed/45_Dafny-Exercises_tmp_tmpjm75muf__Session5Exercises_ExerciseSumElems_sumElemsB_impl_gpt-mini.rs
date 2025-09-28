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
spec fn map_v_to_int(s: Seq<i32>) -> Seq<int> {
    s.map(|i, x| x as int)
}

proof fn map_len_v(s: Seq<i32>)
    ensures map_v_to_int(s).len() == s.len()
{
    let m = map_v_to_int(s);
    assert(m.len() == s.len());
}

proof fn map_index_v(s: Seq<i32>, k: int)
    requires 0 <= k && k < s.len()
    ensures map_v_to_int(s).len() == s.len() && map_v_to_int(s)@[k] == s@[k] as int
{
    let m = map_v_to_int(s);
    assert(m.len() == s.len());
    assert(m@[k] == s@[k] as int);
}

proof fn sum_r_subrange_last(s: Seq<int>, k: int)
    requires 0 <= k && k + 1 <= s.len()
    ensures sum_r(s.subrange(0, k + 1)) == sum_r(s.subrange(0, k)) + s@[k]
{
    let t = s.subrange(0, k + 1);
    if t.len() == 0 {
        assert(false);
    } else {
        assert(sum_r(t) == sum_r(t.subrange(0, t.len() - 1)) + t[t.len() - 1]);
        assert(t.subrange(0, t.len() - 1) == s.subrange(0, k));
        assert(t[t.len() - 1] == s@[k]);
        assert(sum_r(s.subrange(0, k + 1)) == sum_r(s.subrange(0, k)) + s@[k]);
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
    proof { map_len_v(v@); }
    let mut i: usize = 0;
    let mut acc: i32 = 0;
    while i < v.len()
        invariant (i as int) >= 0 && (i as int) <= v.len() as int && acc as int == sum_r(map_v_to_int(v@).subrange(0, i as int))
    {
        let x: i32 = v[i];
        let old_acc = acc;
        acc = acc + x;
        proof {
            // From invariant
            assert(old_acc as int == sum_r(map_v_to_int(v@).subrange(0, i as int)));
            // i is valid index
            assert((i as int) < v.len() as int);
            // relate map and original sequence
            map_index_v(v@, i as int);
            assert(map_v_to_int(v@)@[i as int] == v@@[i as int] as int);
            assert(v@@[i as int] as int == x as int);
            // use lemma to extend sum
            assert((i as int) + 1 <= map_v_to_int(v@).len());
            sum_r_subrange_last(map_v_to_int(v@), i as int);
            assert(old_acc as int + map_v_to_int(v@)@[i as int] == sum_r(map_v_to_int(v@).subrange(0, (i as int) + 1)));
            assert(acc as int == sum_r(map_v_to_int(v@).subrange(0, (i as int) + 1)));
        }
        i = i + 1;
    }
    acc
}
// </vc-code>

fn main() {
}

}