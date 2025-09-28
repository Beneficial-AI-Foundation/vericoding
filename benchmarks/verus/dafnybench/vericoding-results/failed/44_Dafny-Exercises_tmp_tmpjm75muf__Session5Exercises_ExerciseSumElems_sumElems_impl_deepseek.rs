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
proof fn lemma_sum_r_eq_sum_l(s: Seq<int>)
    ensures sum_r(s) == sum_l(s)
    decreases s.len()
{
    if s.len() == 0 {
        assert(sum_r(s) == 0);
        assert(sum_l(s) == 0);
    } else {
        let sub = s.subrange(1, s.len() as int);
        lemma_sum_r_eq_sum_l(sub);
        
        let left_part = s.subrange(0, (s.len() - 1) as int);
        lemma_sum_r_eq_sum_l(left_part);
        
        assert(sum_r(s) == sum_r(left_part) + s[s.len() - 1]);
        assert(sum_l(s) == s[0] + sum_l(sub));
        assert(sum_r(left_part) == sum_l(left_part));
        assert(sum_l(left_part) == s[0] + sum_l(s.subrange(1, (s.len() - 1) as int)));
        assert(sum_r(s) == (s[0] + sum_l(s.subrange(1, (s.len() - 1) as int))) + s[s.len() - 1]);
        assert(sum_l(s) == s[0] + sum_l(sub));
    }
}

proof fn lemma_sum_v_eq_sum_r(v: Seq<int>, c: int, f: int)
    requires 0 <= c <= f <= v.len()
    ensures sum_v(v, c, f) == sum_r(v.subrange(c, f))
{
}

spec fn sum_iter(v: Seq<int>, i: int, acc: int) -> int
    decreases v.len() - i
{
    if i >= v.len() {
        acc
    } else {
        sum_iter(v, i + 1, acc + v[i])
    }
}

proof fn lemma_sum_iter_eq_sum_r(v: Seq<int>, i: int, acc: int)
    requires 0 <= i <= v.len()
    ensures sum_iter(v, i, acc) == acc + sum_r(v.subrange(i, v.len() as int))
    decreases v.len() - i
{
    if i < v.len() {
        lemma_sum_iter_eq_sum_r(v, i + 1, acc + v[i]);
        assert(sum_iter(v, i, acc) == sum_iter(v, i + 1, acc + v[i]));
        assert(sum_r(v.subrange(i, v.len() as int)) == v[i] + sum_r(v.subrange(i + 1, v.len() as int)));
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
    let mut idx: usize = 0;
    
    while idx < v.len()
        invariant
            0 <= idx <= v.len(),
            sum as int == sum_iter(v@.map(|i, x| x as int), idx as int, 0),
    {
        sum = sum + v[idx];
        idx = idx + 1;
    }
    
    proof {
        lemma_sum_iter_eq_sum_r(v@.map(|i, x| x as int), 0, 0);
        assert(sum as int == sum_r(v@.map(|i, x| x as int)));
        lemma_sum_r_eq_sum_l(v@.map(|i, x| x as int));
    }
    
    sum
}
// </vc-code>

fn main() {}

}