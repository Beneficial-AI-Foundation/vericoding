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
proof fn lemma_swap_preserves_multiset(v: Seq<i32>, i: int, j: int)
    requires
        0 <= i < v.len(),
        0 <= j < v.len(),
    ensures
        v.update(i, v[j]).update(j, v[i]).to_multiset() == v.to_multiset(),
{
}

proof fn lemma_subrange_multiset(v: Seq<i32>, start: int, end: int, i: int, j: int)
    requires
        0 <= start <= i < end <= v.len(),
        0 <= start <= j < end <= v.len(),
    ensures
        v.subrange(start, end).update(i - start, v[j]).update(j - start, v[i]).to_multiset() == v.subrange(start, end).to_multiset(),
{
    lemma_swap_preserves_multiset(v.subrange(start, end), i - start, j - start);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn separate(v: &mut Vec<i32>) -> (i: usize)
    ensures
        0 <= i <= v.len(),
        positive(v@.subrange(0, i as int)),
        strict_negative(v, i, v.len()),
        is_permutation(v@, old(v)@),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut i: usize = 0;
    let mut j: usize = v.len();
    
    while i < j
        invariant
            0 <= i <= j <= v.len(),
            positive(v@.subrange(0, i as int)),
            strict_negative(v, j, v.len()),
            is_permutation(v@, old(v)@),
        decreases j - i
    {
        if v[i] < 0 {
            j = j - 1;
            let temp = v[i];
            let ghost old_v = v@;
            // Perform the swap in a way that avoids borrow conflicts
            let val_j = v[j];
            v.set(i, val_j);
            v.set(j, temp);
            proof {
                lemma_subrange_multiset(old_v, 0, v.len() as int, i as int, j as int);
            }
        } else {
            i = i + 1;
        }
    }
    i
}
// </vc-code>

fn main() {}

}