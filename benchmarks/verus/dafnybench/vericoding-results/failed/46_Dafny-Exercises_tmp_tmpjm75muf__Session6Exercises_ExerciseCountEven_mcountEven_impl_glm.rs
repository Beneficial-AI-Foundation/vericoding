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
proof fn lemma_count_even_append(s1: Seq<int>, s2: Seq<int>, b: int)
    requires positive(s1),
    requires positive(s2),
    requires s2.len() == 1,
    requires s2[0] == b,
    ensures count_even(s1 + s2) == count_even(s1) + (if b % 2 == 0 { 1 } else { 0 })
{
    if s1.len() == 0 {
        assert(s1 + s2 == s2);
        assert(count_even(s1 + s2) == count_even(s2));
        assert(count_even(s2) == (if b % 2 == 0 { 1 } else { 0 }));
        assert(count_even(s1) == 0);
    } else {
        let total_len = s1.len() + s2.len();
        let last_index = total_len - 1;
        assert((s1+s2)[last_index] == b);
        assert((s1+s2).subrange(0, last_index) == s1);
        // By the definition of count_even:
        //   count_even(s1+s2) = (if (s1+s2)[last_index] % 2 == 0 {1} else {0}) + count_even((s1+s2).subrange(0, last_index))
        //   = (if b % 2 == 0 {1} else {0}) + count_even(s1)
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
    let mut count = 0;
    let mut i = 0;
    
    while i < v.len()
        invariant 0 <= i <= v.len()
        invariant positive(v@.map(|i: int, x: i32| x as int).subrange(0, i))
        invariant count as int == count_even(v@.map(|i: int, x: i32| x as int).subrange(0, i))
    {
        let elem = v[i] as int;
        
        if is_even(elem) {
            count = count + 1;
        }
        
        proof {
            let the_rest = v@.map(|i: int, x: i32| x as int).subrange(0, i);
            let new_elem = v@.map(|i: int, x: i32| x as int)[i];
            assert(new_elem >= 0);
            lemma_count_even_append(the_rest, seq![new_elem], new_elem);
            assert(v@.map(|i: int, x: i32| x as int).subrange(0, i + 1) == the_rest + seq![new_elem]);
            assert(positive(the_rest + seq![new_elem]));
            assert(count_even(v@.map(|i: int, x: i32| x as int).subrange(0, i + 1)) == 
                   count_even(the_rest) + (if new_elem % 2 == 0 { 1 } else { 0 }));
        }
        
        i = i + 1;
    }
    
    count
}
// </vc-code>

fn main() {
}

}