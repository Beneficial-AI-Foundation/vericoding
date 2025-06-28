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
            // Sorted property
            sorted_slice(b, start, k as int),
            // Boundary conditions - elements in b are <= next elements to be added
            i1 < a1.len() ==> (k as int == start || b.spec_index(k as int - 1) <= a1.spec_index(i1 as int)),
            i2 < a2.len() ==> (k as int == start || b.spec_index(k as int - 1) <= a2.spec_index(i2 as int))
    {
        if a1.spec_index(i1 as int) <= a2.spec_index(i2 as int) {
            let val = a1.spec_index(i1 as int);
            b.set(k, val);
            
            proof {
                // Prove multiset property
                assert(a1.spec_subrange(0, (i1 + 1) as int) == 
                       a1.spec_subrange(0, i1 as int).push(val));
                
                // Prove sorted property is maintained
                if k as int > start {
                    assert(sorted_seq(a1));
                    if i1 > 0 {
                        assert(a1.spec_index((i1 - 1) as int) <= a1.spec_index(i1 as int));
                    }
                }
            }
            
            i1 = i1 + 1;
        } else {
            let val = a2.spec_index(i2 as int);
            b.set(k, val);
            
            proof {
                // Prove multiset property
                assert(a2.spec_subrange(0, (i2 + 1) as int) == 
                       a2.spec_subrange(0, i2 as int).push(val));
                
                // Prove sorted property is maintained
                if k as int > start {
                    assert(sorted_seq(a2));
                    if i2 > 0 {
                        assert(a2.spec_index((i2 - 1) as int) <= a2.spec_index(i2 as int));
                    }
                }
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
            i1 < a1.len() ==> (k as int == start || b.spec_index(k as int - 1) <= a1.spec_index(i1 as int))
    {
        let val = a1.spec_index(i1 as int);
        b.set(k, val);
        
        proof {
            // Prove multiset and sorted properties
            assert(a1.spec_subrange(0, (i1 + 1) as int) == 
                   a1.spec_subrange(0, i1 as int).push(val));
            
            if k as int > start {
                assert(sorted_seq(a1));
            }
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
            i2 < a2.len() ==> (k as int == start || b.spec_index(k as int - 1) <= a2.spec_index(i2 as int))
    {
        let val = a2.spec_index(i2 as int);
        b.set(k, val);
        
        proof {
            // Prove multiset and sorted properties
            assert(a2.spec_subrange(0, (i2 + 1) as int) == 
                   a2.spec_subrange(0, i2 as int).push(val));
            
            if k as int > start {
                assert(sorted_seq(a2));
            }
        }
        
        i2 = i2 + 1;
        k = k + 1;
    }
    
    proof {
        // Final verification
        assert(i1 == a1.len());
        assert(i2 == a2.len());
        assert(k as int == end);
        assert(a1.spec_subrange(0, a1.len()) == a1);
        assert(a2.spec_subrange(0, a2.len()) == a2);
    }
}

}