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
proof fn count_even_index(s: Seq<int>)
    requires
        positive(s),
    ensures
        forall|i: int| 0 <= i < s.len() ==> (if s[i] % 2 == 0 {1} else {0}) as int == count_even(s.subrange(i, i+1)),
    decreases s.len()
{
    if s.len() > 0 {
        let sub = s.subrange(0, s.len() - 1);
        count_even_index(sub);
        
        assert forall|i: int| 0 <= i < s.len() implies (if s[i] % 2 == 0 {1} else {0}) as int == count_even(s.subrange(i, i+1)) by {
            if i == s.len() - 1 {
                assert(s.subrange(i, i+1) =~= Seq::new(1, |j: int| s[j + i]));
                assert(s[i] == s.subrange(i, i+1)[0]);
            } else {
                assert(i < s.len() - 1);
                assert(positive(sub));
                assert(sub.subrange(i, i+1) =~= s.subrange(i, i+1));
            }
        };
    }
}

proof fn count_even_nonnegative(s: Seq<int>)
    requires
        positive(s),
    ensures
        count_even(s) >= 0,
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        let sub = s.subrange(0, s.len() - 1);
        count_even_nonnegative(sub);
    }
}

proof fn count_even_recursive(s: Seq<int>)
    requires
        positive(s),
    ensures
        s.len() > 0 ==> count_even(s) == count_even(s.subrange(0, s.len()-1)) + (if s[s.len()-1] % 2 == 0 {1} else {0}) as int,
    decreases s.len()
{
    if s.len() > 0 {
        let last = s[s.len() - 1];
        let sub = s.subrange(0, s.len() - 1);
        
        // Base case: single element
        if s.len() == 1 {
            assert(s.subrange(0, 0).len() == 0);
            assert(count_even(s.subrange(0, 0)) == 0);
        }
        
        // Recursive case follows from definition
    }
}

proof fn count_even_monotonic(s1: Seq<int>, s2: Seq<int>)
    requires
        positive(s1),
        positive(s2),
        s1 =~= s2 + s2,
    ensures
        count_even(s1) == 2 * count_even(s2),
    decreases s2.len()
{
    if s2.len() == 0 {
        assert(s1 =~= Seq::empty());
    } else {
        let s2_sub = s2.subrange(0, s2.len() - 1);
        let s1_sub = s1.subrange(0, s1.len() - 2);
        count_even_monotonic(s1_sub, s2_sub);
        
        let last = s2[s2.len() - 1];
        count_even_recursive(s1);
        count_even_recursive(s2);
    }
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
    let s = ghost!(v@.map(|j: int, x: i32| x as int));
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            positive(v@.map(|k: int, x: i32| x as int).subrange(0, i)),
            n as int == count_even(v@.map(|k: int, x: i32| x as int).subrange(0, i)),
        decreases v.len() - i,
    {
        let s_val = v@.map(|k: int, x: i32| x as int);
        let elem = v[i];
        
        assert(elem as int >= 0) by {
            assert(positive(s_val));
            assert(0 <= i < s_val.len());
        };
        
        proof {
            count_even_index(s_val.subrange(0, i + 1));
            count_even_recursive(s_val.subrange(0, i + 1));
            assert(s_val.subrange(0, i + 1) =~= s_val.subrange(0, i) + Seq::new(1, |j: int| s_val[i]));
        }
        
        if elem % 2 == 0 {
            n = n + 1;
        }
        
        i = i + 1;
        
        proof {
            assert forall|j: int| 0 <= j < i implies #[trigger] s_val[j] >= 0 by {
                assert(positive(s_val));
            };
        }
    }
    
    n
}
// </vc-code>

fn main() {
}

}