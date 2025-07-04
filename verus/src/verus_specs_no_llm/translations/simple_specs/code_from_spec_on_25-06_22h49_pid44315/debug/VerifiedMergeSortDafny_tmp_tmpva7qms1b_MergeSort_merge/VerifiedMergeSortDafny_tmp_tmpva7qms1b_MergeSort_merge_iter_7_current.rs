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
            forall |i: int, j: int| start <= i <= j < k as int ==> b.spec_index(i) <= b.spec_index(j),
            // Additional invariant: if we've placed elements, the last one is <= remaining elements
            k as int > start ==> (
                (i1 < a1.len() ==> b.spec_index(k as int - 1) <= a1.spec_index(i1 as int)) &&
                (i2 < a2.len() ==> b.spec_index(k as int - 1) <= a2.spec_index(i2 as int))
            )
    {
        if a1.spec_index(i1 as int) <= a2.spec_index(i2 as int) {
            b.set(k, a1.spec_index(i1 as int));
            
            // Proof that sortedness is maintained
            assert(forall |i: int| start <= i < k as int ==> 
                b.spec_index(i) <= a1.spec_index(i1 as int)) by {
                if k as int > start {
                    assert(b.spec_index(k as int - 1) <= a1.spec_index(i1 as int));
                    assert(forall |i: int| start <= i < k as int - 1 ==> 
                        b.spec_index(i) <= b.spec_index(k as int - 1));
                }
            };
            
            i1 = i1 + 1;
        } else {
            b.set(k, a2.spec_index(i2 as int));
            
            // Proof that sortedness is maintained
            assert(forall |i: int| start <= i < k as int ==> 
                b.spec_index(i) <= a2.spec_index(i2 as int)) by {
                if k as int > start {
                    assert(b.spec_index(k as int - 1) <= a2.spec_index(i2 as int));
                    assert(forall |i: int| start <= i < k as int - 1 ==> 
                        b.spec_index(i) <= b.spec_index(k as int - 1));
                }
            };
            
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
            forall |i: int, j: int| start <= i <= j < k as int ==> b.spec_index(i) <= b.spec_index(j),
            // Sortedness between existing and remaining elements
            k as int > start && i1 < a1.len() ==> b.spec_index(k as int - 1) <= a1.spec_index(i1 as int)
    {
        b.set(k, a1.spec_index(i1 as int));
        
        // Proof that sortedness is maintained
        assert(forall |i: int| start <= i < k as int ==> 
            b.spec_index(i) <= a1.spec_index(i1 as int)) by {
            if k as int > start {
                assert(b.spec_index(k as int - 1) <= a1.spec_index(i1 as int));
            }
        };
        
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
            forall |i: int, j: int| start <= i <= j < k as int ==> b.spec_index(i) <= b.spec_index(j),
            // Sortedness between existing and remaining elements
            k as int > start && i2 < a2.len() ==> b.spec_index(k as int - 1) <= a2.spec_index(i2 as int)
    {
        b.set(k, a2.spec_index(i2 as int));
        
        // Proof that sortedness is maintained
        assert(forall |i: int| start <= i < k as int ==> 
            b.spec_index(i) <= a2.spec_index(i2 as int)) by {
            if k as int > start {
                assert(b.spec_index(k as int - 1) <= a2.spec_index(i2 as int));
            }
        };
        
        i2 = i2 + 1;
        k = k + 1;
    }
    
    // Final assertions to help prove postconditions
    assert(i1 == a1.len() && i2 == a2.len());
    assert(k as int == end);
    assert(b.spec_subrange(start, end).to_multiset() == 
        a1.to_multiset().add(a2.to_multiset()));
}

}