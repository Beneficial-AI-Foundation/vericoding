use vstd::prelude::*;

verus! {

spec fn strict_negative(v: &Vec<i32>, i: usize, j: usize) -> bool
    recommends 0 <= i <= j <= v.len()
{
    forall|u: usize| i <= u < j ==> v[u as int] < 0
}

spec fn positive(s: Seq<i32>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

spec fn is_permutation(s: Seq<i32>, t: Seq<i32>) -> bool {
    s.to_multiset() == t.to_multiset()
}

/**
returns an index st new array is a permutation of the old array
positive first and then strictnegative, i is the firs neg or len if not any */

// <vc-helpers>
spec fn is_negative(x: i32) -> bool {
    x < 0
}

proof fn swap_preserves_multiset(v: &mut Vec<i32>, i: usize, j: usize) 
    requires
        0 <= i < v.len(),
        0 <= j < v.len(),
    ensures
        v@.to_multiset() == old(v)@.to_multiset(),
{
    v.swap(i, j);
}

proof fn loop_invariant(v: &Vec<i32>, i: usize, j: usize, old_seq: Seq<i32>)
    requires
        0 <= i <= j <= v.len(),
        positive(v@.subrange(0, i)),
        forall|u: usize| i <= u < j ==> is_negative(v@[u]),
        v@.to_multiset() == old_seq.to_multiset(),
    ensures
        0 <= i <= j <= v.len(),
        positive(v@.subrange(0, i)),
        strict_negative(v, i, j),
        is_permutation(v@, old_seq),
{
    assert forall|u: usize| i <= u < j implies v[u] < 0 by {
        assert(v@[u] < 0);
    };
}
// </vc-helpers>

// <vc-spec>
fn separate(v: &mut Vec<i32>) -> (i: usize)
    ensures
        0 <= i <= v.len(),
        positive(v@.subrange(0, i as int)),
        strict_negative(v, i, v.len()),
        is_permutation(v@, old(v)@),
// </vc-spec>
// <vc-code>
{
    let old_v = old(v)@;
    let mut i: usize = 0;
    let mut j: usize = 0;
    
    while j < v.len()
        invariant
            0 <= i <= j <= v.len(),
            positive(v@.subrange(0, i)),
            forall|u: usize| i <= u < j ==> is_negative(v@[u]),
            v@.to_multiset() == old_v.to_multiset(),
        decreases v.len() - j,
    {
        let current = v[j];
        if current >= 0 {
            if i != j {
                proof { swap_preserves_multiset(v, i, j); }
                v.swap(i, j);
            }
            i += 1;
            j += 1;
        } else {
            j += 1;
        }
        
        proof { loop_invariant(v, i, j, old_v); }
    }
    
    proof {
        assert forall|u: usize| i <= u < v.len() implies v[u] < 0 by {
            assert(forall|u: usize| i <= u < j ==> v@[u] < 0);
            assert(j == v.len());
        };
    }
    
    i
}
// </vc-code>

fn main() {}

}