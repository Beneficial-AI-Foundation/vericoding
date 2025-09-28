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
proof fn sum_r_empty()
    ensures forall|s: Seq<int>| s.len() == 0 ==> sum_r(s) == 0
{
}

proof fn sum_r_append(s: Seq<int>, x: int)
    ensures sum_r(s.push(x)) == sum_r(s) + x
    decreases s.len()
{
    let s_new = s.push(x);
    assert(s_new.len() == s.len() + 1);
    assert(s_new[s_new.len() - 1] == x);
    assert(s_new.subrange(0, s_new.len() - 1) =~= s);
}

proof fn sum_r_subrange_append(v: Seq<int>, i: int, j: int)
    requires 0 <= i <= j < v.len()
    ensures sum_r(v.subrange(i, j + 1)) == sum_r(v.subrange(i, j)) + v[j]
{
    let sub = v.subrange(i, j + 1);
    assert(sub.len() == j + 1 - i);
    assert(sub[sub.len() - 1] == v[j]);
    assert(sub.subrange(0, sub.len() - 1) =~= v.subrange(i, j));
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
            sum as int == sum_r(v@.subrange(0, i as int).map(|idx: int, x: i32| x as int)),
            forall|j: int| 0 <= j < i ==> sum as int + v@[j] as int == sum as int + v@[j] as int,
        decreases v.len() - i
    {
        proof {
            let mapped_seq = v@.subrange(0, i as int).map(|idx: int, x: i32| x as int);
            let next_elem = v@[i as int];
            let next_subrange = v@.subrange(0, (i + 1) as int);
            let next_mapped_seq = next_subrange.map(|idx: int, x: i32| x as int);
            
            assert(next_subrange =~= v@.subrange(0, i as int).push(next_elem));
            assert(next_mapped_seq =~= mapped_seq.push(next_elem as int));
            sum_r_append(mapped_seq, next_elem as int);
            assert(sum_r(next_mapped_seq) == sum_r(mapped_seq) + next_elem as int);
        }
        
        sum = (sum as i64 + v[i] as i64) as i32;
        i = i + 1;
    }
    
    proof {
        assert(i == v.len());
        assert(v@.subrange(0, v@.len() as int) =~= v@);
        assert(v@.subrange(0, v@.len() as int).map(|idx: int, x: i32| x as int) 
               =~= v@.map(|idx: int, x: i32| x as int));
    }
    
    sum
}
// </vc-code>

fn main() {}

}