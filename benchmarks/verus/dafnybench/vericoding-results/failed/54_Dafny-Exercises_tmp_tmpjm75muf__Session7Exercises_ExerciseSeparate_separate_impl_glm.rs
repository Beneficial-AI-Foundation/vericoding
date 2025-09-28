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
proof fn lemma_permutation_append<T>(s1: Seq<T>, s2: Seq<T>)
    ensures
        s1.to_multiset().union(s2.to_multiset()) == (s1 + s2).to_multiset(),
{
    assert((s1 + s2).to_multiset() == s1.to_multiset().union(s2.to_multiset()));
}

proof fn lemma_permutation_swap<T>(s: Vec<T>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        s.update(i, s[j]).update(j, s[i]).to_multiset() =~= s.to_multiset(),
{
    assert(s.update(i, s[j]).update(j, s[i]).to_multiset() =~= s.to_multiset());
}

proof fn lemma_permutation_preserved_by_swap<T>(v: &Vec<T>, i: usize, j: usize)
    requires
        0 <= i < v.len(),
        0 <= j < v.len(),
    ensures
        v@.update(i as int, v@[j as int]).update(j as int, v@[i as int]).to_multiset() =~= v@.to_multiset(),
{
    lemma_permutation_swap(v@, i as int, j as int);
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
    let mut low = 0;
    let mut high = v.len();
    
    while low < high
        invariant
            0 <= low <= high <= v.len(),
            positive(v@.subrange(0, low as int)),
            strict_negative(v, high, v.len()),
            is_permutation(v@, old(v)@),
    {
        if v[low] >= 0 {
            low += 1;
        } else {
            high -= 1;
            v.swap(low, high);
            proof {
                lemma_permutation_preserved_by_swap(v, low, high);
            }
        }
    }
    low
}
// </vc-code>

fn main() {}

}