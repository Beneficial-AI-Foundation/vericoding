use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

spec fn is_even(i: int) -> bool
    recommends i >= 0
{
    i % 2 == 0
}

spec fn count_even(s: Seq<int>) -> int
    recommends positive(s)
    decreases s.len()
{
    if s.len() == 0 {
        0 as int
    } else {
        (if s[s.len() - 1] % 2 == 0 { 1 as int } else { 0 as int }) + count_even(s.subrange(0, s.len() - 1))
    }
}

// <vc-helpers>
proof fn count_even_subrange_plus_one(s: Seq<int>, i: int)
    requires 
        positive(s),
        0 <= i < s.len(),
    ensures
        count_even(s.subrange(0, i + 1)) == count_even(s.subrange(0, i)) + if s[i] % 2 == 0 { 1int } else { 0int }
    decreases s.len() - i
{
    let sub_i = s.subrange(0, i);
    let sub_i_plus_1 = s.subrange(0, i + 1);
    
    assert(sub_i_plus_1.len() == i + 1);
    assert(sub_i_plus_1[sub_i_plus_1.len() - 1] == s[i]);
    assert(sub_i_plus_1.subrange(0, sub_i_plus_1.len() - 1) =~= sub_i);
}

proof fn count_even_full(s: Seq<int>)
    requires positive(s)
    ensures count_even(s) == count_even(s.subrange(0, s.len() as int))
{
    assert(s =~= s.subrange(0, s.len() as int));
}
// </vc-helpers>

// <vc-spec>
fn mcount_even(v: &Vec<i32>) -> (n: i32)
    requires positive(v@.map(|i: int, x: i32| x as int))
    ensures n as int == count_even(v@.map(|i: int, x: i32| x as int))
// </vc-spec>
// <vc-code>
{
    let mut n: i32 = 0;
    let mut i: usize = 0;
    let ghost s = v@.map(|i: int, x: i32| x as int);
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            s == v@.map(|i: int, x: i32| x as int),
            positive(s),
            n as int == count_even(s.subrange(0, i as int)),
            n >= 0,
            n <= i as i32
        decreases v.len() - i
    {
        let old_n = n;
        if v[i] % 2 == 0 {
            n = n + 1;
        }
        
        proof {
            count_even_subrange_plus_one(s, i as int);
            assert(n as int == old_n as int + if v[i] % 2 == 0 { 1int } else { 0int });
            assert(n as int == count_even(s.subrange(0, i as int)) + if s[i as int] % 2 == 0 { 1int } else { 0int });
            assert(n as int == count_even(s.subrange(0, (i + 1) as int)));
        }
        
        i = i + 1;
    }
    
    proof {
        count_even_full(s);
    }
    
    n
}
// </vc-code>

fn main() {
}

}