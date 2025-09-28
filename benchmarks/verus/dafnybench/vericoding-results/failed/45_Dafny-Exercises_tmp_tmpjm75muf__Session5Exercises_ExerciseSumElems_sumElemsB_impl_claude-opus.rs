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
proof fn sum_r_empty(s: Seq<int>)
    ensures s.len() == 0 ==> sum_r(s) == 0
{
}

proof fn sum_r_append(s: Seq<int>, x: int)
    ensures sum_r(s.push(x)) == sum_r(s) + x
    decreases s.len()
{
    reveal(sum_r);
    let s_new = s.push(x);
    assert(s_new.len() == s.len() + 1);
    assert(s_new[s_new.len() - 1] == x);
    assert(s_new.subrange(0, s_new.len() - 1) =~= s);
}

proof fn sum_r_subrange_extend(v: Seq<int>, i: int, j: int)
    requires 0 <= i < j <= v.len()
    ensures sum_r(v.subrange(i, j)) == sum_r(v.subrange(i, j - 1)) + v[j - 1]
{
    reveal(sum_r);
    let s = v.subrange(i, j);
    assert(s.len() == j - i);
    assert(s[s.len() - 1] == v[j - 1]);
    assert(s.subrange(0, s.len() - 1) =~= v.subrange(i, j - 1));
}
// </vc-helpers>

// <vc-spec>
fn sum_elems_b(v: &[i32]) -> (sum: i32)
//ensures sum as int == sum_l(v@.map(|i, x| x as int))
ensures sum as int == sum_r(v@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            sum as int == sum_r(v@.map(|idx: int, x: i32| x as int).subrange(0, i as int)),
            forall|j: int| 0 <= j < i ==> -2147483648 <= sum_r(v@.map(|idx: int, x: i32| x as int).subrange(0, j + 1)) <= 2147483647,
            i < v.len() ==> -2147483648 <= sum as int + v[i as int] as int <= 2147483647,
        decreases v.len() - i
    {
        let old_sum = sum;
        sum = sum + v[i];
        i = i + 1;
        
        proof {
            let v_seq = v@.map(|idx: int, x: i32| x as int);
            sum_r_subrange_extend(v_seq, 0, i as int);
            assert(v_seq.subrange(0, i as int).len() == i as int);
            assert(v_seq[(i - 1) as int] == v[(i - 1) as int] as int);
            assert(old_sum as int == sum_r(v_seq.subrange(0, (i - 1) as int)));
            assert(sum as int == old_sum as int + v[(i - 1) as int] as int);
            assert(sum as int == sum_r(v_seq.subrange(0, i as int)));
        }
    }
    
    proof {
        let v_seq = v@.map(|idx: int, x: i32| x as int);
        assert(i == v.len());
        assert(v_seq.subrange(0, v.len() as int) =~= v_seq);
    }
    
    sum
}
// </vc-code>

fn main() {
}

}