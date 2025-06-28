use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted_seq(a: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i <= j < a.len() ==> a.spec_index(i) <= a.spec_index(j)
}

spec fn sorted_slice(a: &Vec<int>, start: int, end: int) -> bool
    requires 0 <= start <= end <= a.len()
{
    forall |i: int, j: int| start <= i <= j < end ==> a.spec_index(i) <= a.spec_index(j)
}

spec fn merged(a1: Seq<int>, a2: Seq<int>, b: &Vec<int>, start: int, end: int) -> bool
    requires 0 <= start <= end <= b.len()
    requires end - start == a1.len() + a2.len()
{
    a1.to_multiset().add(a2.to_multiset()) == b.spec_subrange(start, end).to_multiset()
}

proof fn lemma_multiset_append(s1: Seq<int>, s2: Seq<int>, x: int)
    ensures s1.push(x).to_multiset() == s1.to_multiset().insert(x)
{
    // This is a fundamental property of multisets and sequences
    assert(s1.push(x).to_multiset() =~= s1.to_multiset().insert(x));
}

proof fn lemma_subrange_extend(v: &Vec<int>, start: int, end: int, x: int)
    requires 0 <= start <= end < v.len()
    requires v.spec_index(end) == x
    ensures v.spec_subrange(start, end + 1) == v.spec_subrange(start, end).push(x)
{
    // This follows from the definition of subrange
    assert(v.spec_subrange(start, end + 1) =~= v.spec_subrange(start, end).push(x));
}

proof fn lemma_sorted_extend(v: &Vec<int>, start: int, end: int, x: int)
    requires 0 <= start <= end < v.len()
    requires sorted_slice(v, start, end)
    requires end > start ==> v.spec_index(end - 1) <= x
    requires v.spec_index(end) == x
    ensures sorted_slice(v, start, end + 1)
{
    if start < end + 1 {
        assert forall |i: int, j: int| start <= i <= j < end + 1 implies v.spec_index(i) <= v.spec_index(j) by {
            if j < end {
                // Both i and j are in the original range
                assert(v.spec_index(i) <= v.spec_index(j));
            } else if j == end {
                if i < end {
                    // i is in original range, j is the new element
                    if end > start {
                        assert(v.spec_index(i) <= v.spec_index(end - 1));
                        assert(v.spec_index(end - 1) <= x);
                        assert(v.spec_index(end) == x);
                        assert(v.spec_index(i) <= v.spec_index(j));
                    }
                } else {
                    // Both i and j are the new element
                    assert(i == end && j == end);
                    assert(v.spec_index(i) <= v.spec_index(j));
                }
            }
        }
    }
}

proof fn lemma_subrange_multiset_property(s1: Seq<int>, s2: Seq<int>, x: int, i1: int, i2: int)
    requires 0 <= i1 <= s1.len()
    requires 0 <= i2 <= s2.len()
    ensures s1.spec_subrange(0, i1).push(x).to_multiset().add(s2.spec_subrange(0, i2).to_multiset()) == 
            s1.spec_subrange(0, i1).to_multiset().add(s2.spec_subrange(0, i2).to_multiset()).insert(x)
{
    lemma_multiset_append(s1.spec_subrange(0, i1), s2.spec_subrange(0, i2), x);
}

fn merge(a1: Seq<int>, a2: Seq<int>, start: int, end: int, b: &mut Vec<int>)
    requires 
        0 <= start <= end <= old(b).len(),
        end - start == a1.len() + a2.len(),
        sorted_seq(a1),
        sorted_seq(a2)
    ensures 
        b.len() == old(b).len(),
        merged(a1, a2, b, start, end),
        sorted_slice(b, start, end)
{
    let mut i1: usize = 0;
    let mut i2: usize = 0;
    let mut k: usize = start as usize;
    
    // Merge the two sequences
    while i1 < a1.len() && i2 < a2.len()
        invariant
            0 <= i1 <= a1.len(),
            0 <= i2 <= a2.len(),
            k as int == start + i1 as int + i2 as int,
            start <= k as int <= end <= b.len(),
            b.len() == old(b).len(),
            // Multiset property - elements placed so far
            b.spec_subrange(start, k as int).to_multiset() == 
                a1.spec_subrange(0, i1 as int).to_multiset().add(
                    a2.spec_subrange(0, i2 as int).to_multiset()
                ),
            // Sorted property for the portion filled so far
            sorted_slice(b, start, k as int),
            // Transition invariant: last element is compatible with remaining
            k as int > start ==> (
                (i1 < a1.len() ==> b.spec_index(k as int - 1) <= a1.spec_index(i1 as int)) &&
                (i2 < a2.len() ==> b.spec_index(k as int - 1) <= a2.spec_index(i2 as int))
            )
    {
        if a1.spec_index(i1 as int) <= a2.spec_index(i2 as int) {
            b.set(k, a1.spec_index(i1 as int));
            
            // Prove multiset property
            proof {
                lemma_subrange_extend(b, start, k as int, a1.spec_index(i1 as int));
                
                // Show that adding a1[i1] maintains the multiset invariant
                assert(a1.spec_subrange(0, i1 as int + 1) == a1.spec_subrange(0, i1 as int).push(a1.spec_index(i1 as int)));
                lemma_multiset_append(a1.spec_subrange(0, i1 as int), a2.spec_subrange(0, i2 as int), a1.spec_index(i1 as int));
            }
            
            // Prove sorted property
            proof {
                if k as int > start {
                    // The element we're adding is >= the last element
                    assert(b.spec_index(k as int - 1) <= a1.spec_index(i1 as int));
                }
                lemma_sorted_extend(b, start, k as int, a1.spec_index(i1 as int));
            }
            
            i1 = i1 + 1;
        } else {
            b.set(k, a2.spec_index(i2 as int));
            
            // Prove multiset property
            proof {
                lemma_subrange_extend(b, start, k as int, a2.spec_index(i2 as int));
                
                // Show that adding a2[i2] maintains the multiset invariant
                assert(a2.spec_subrange(0, i2 as int + 1) == a2.spec_subrange(0, i2 as int).push(a2.spec_index(i2 as int)));
                lemma_multiset_append(a2.spec_subrange(0, i2 as int), a1.spec_subrange(0, i1 as int), a2.spec_index(i2 as int));
            }
            
            // Prove sorted property
            proof {
                if k as int > start {
                    // The element we're adding is >= the last element
                    assert(b.spec_index(k as int - 1) <= a2.spec_index(i2 as int));
                }
                lemma_sorted_extend(b, start, k as int, a2.spec_index(i2 as int));
            }
            
            i2 = i2 + 1;
        }
        k = k + 1;
    }
    
    // Copy remaining elements from a1
    while i1 < a1.len()
        invariant
            0 <= i1 <= a1.len(),
            i2 == a2.len(),
            k as int == start + i1 as int + i2 as int,
            start <= k as int <= end <= b.len(),
            b.len() == old(b).len(),
            b.spec_subrange(start, k as int).to_multiset() == 
                a1.spec_subrange(0, i1 as int).to_multiset().add(a2.to_multiset()),
            sorted_slice(b, start, k as int),
            // Transition invariant
            k as int > start && i1 < a1.len() ==> b.spec_index(k as int - 1) <= a1.spec_index(i1 as int)
    {
        b.set(k, a1.spec_index(i1 as int));
        
        proof {
            lemma_subrange_extend(b, start, k as int, a1.spec_index(i1 as int));
            assert(a1.spec_subrange(0, i1 as int + 1) == a1.spec_subrange(0, i1 as int).push(a1.spec_index(i1 as int)));
            lemma_multiset_append(a1.spec_subrange(0, i1 as int), a2.to_multiset(), a1.spec_index(i1 as int));
            lemma_sorted_extend(b, start, k as int, a1.spec_index(i1 as int));
        }
        
        i1 = i1 + 1;
        k = k + 1;
    }
    
    // Copy remaining elements from a2
    while i2 < a2.len()
        invariant
            0 <= i2 <= a2.len(),
            i1 == a1.len(),
            k as int == start + i1 as int + i2 as int,
            start <= k as int <= end <= b.len(),
            b.len() == old(b).len(),
            b.spec_subrange(start, k as int).to_multiset() == 
                a1.to_multiset().add(a2.spec_subrange(0, i2 as int).to_multiset()),
            sorted_slice(b, start, k as int),
            // Transition invariant
            k as int > start && i2 < a2.len() ==> b.spec_index(k as int - 1) <= a2.spec_index(i2 as int)
    {
        b.set(k, a2.spec_index(i2 as int));
        
        proof {
            lemma_subrange_extend(b, start, k as int, a2.spec_index(i2 as int));
            assert(a2.spec_subrange(0, i2 as int + 1) == a2.spec_subrange(0, i2 as int).push(a2.spec_index(i2 as int)));
            lemma_multiset_append(a2.spec_subrange(0, i2 as int), a1.to_multiset(), a2.spec_index(i2 as int));
            lemma_sorted_extend(b, start, k as int, a2.spec_index(i2 as int));
        }
        
        i2 = i2 + 1;
        k = k + 1;
    }
    
    // Final proof that we've merged everything correctly
    proof {
        assert(i1 == a1.len());
        assert(i2 == a2.len());
        assert(k as int == end);
        assert(a1.spec_subrange(0, i1 as int) == a1);
        assert(a2.spec_subrange(0, i2 as int) == a2);
    }
}

}