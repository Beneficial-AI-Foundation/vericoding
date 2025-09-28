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
spec fn is_partitioned(v: Seq<i32>, i: int) -> bool {
    positive(v.subrange(0, i)) && strict_negative(v, i as usize, v.len() as usize)
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
    let ghost old_v = old(v)@;
    let mut i = 0u32;
    let mut j = v.len() as u32;
    while i < j
        invariant 0 <= i <= j <= v.len(),
                 positive(v@.subrange(0, i as int)),
                 strict_negative(v@, j as usize, v@.len() as usize),
                 v@.to_multiset() == old_v.to_multiset(),
    {
        if v[i as usize] >= 0 {
            i = i + 1;
        } else if v[(j - 1) as usize] < 0 {
            j = j - 1;
        } else {
            let temp = v[i as usize];
            v[i as usize] = v[(j - 1) as usize];
            v[(j - 1) as usize] = temp;
            i = i + 1;
            proof { // Multiset remains the same
                assert(v@.to_multiset() == old(_.to_multiset()));
            }
            j = j - 1;
        }
    }
    proof { // Ensure postcondition for positives and negatives
        assert(positive(v@.subrange(0, i as int)));
        assert(strict_negative(v@, i as usize, v@.len() as usize));
    }
    i as usize
}
// </vc-code>

fn main() {}

}