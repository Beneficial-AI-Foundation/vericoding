use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sorted(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < q.len() ==> q.index(i) <= q.index(j)
}

fn Merge(mut b: Vec<int>, c: &Vec<int>, d: &Vec<int>) -> (result: Vec<int>)
    requires
        b.len() == c.len() + d.len(),
        Sorted(c@),
        Sorted(d@)
    ensures
        Sorted(result@),
        multiset(result@) == multiset(c@) + multiset(d@)
{
    let mut i = 0;
    let mut j = 0;
    let mut k = 0;
    
    while i < c.len() && j < d.len()
        invariant
            0 <= i <= c.len(),
            0 <= j <= d.len(),
            k == i + j,
            k <= b.len(),
            Sorted(b@.subrange(0, k as int)),
            multiset(b@.subrange(0, k as int)) == 
                multiset(c@.subrange(0, i as int)) + multiset(d@.subrange(0, j as int)),
            // Elements in merged part are <= remaining elements
            forall|x: int| 0 <= x < k && i < c.len() ==> b@.index(x) <= c@.index(i as int),
            forall|x: int| 0 <= x < k && j < d.len() ==> b@.index(x) <= d@.index(j as int),
    {
        if c[i] <= d[j] {
            b.set(k, c[i]);
            
            // Prove that sortedness is maintained
            assert(Sorted(b@.subrange(0, (k + 1) as int))) by {
                if k > 0 {
                    // Previous element is <= c[i] by invariant
                    assert(b@.index(k as int - 1) <= c@.index(i as int));
                }
                // All elements before k are sorted (invariant)
                // Element at k is c[i], which maintains order
                assert(forall|x: int, y: int| 0 <= x <= y < (k + 1) as int ==> 
                    b@.subrange(0, (k + 1) as int).index(x) <= b@.subrange(0, (k + 1) as int).index(y));
            };
            
            i = i + 1;
        } else {
            b.set(k, d[j]);
            
            // Prove that sortedness is maintained
            assert(Sorted(b@.subrange(0, (k + 1) as int))) by {
                if k > 0 {
                    // Previous element is <= d[j] by invariant
                    assert(b@.index(k as int - 1) <= d@.index(j as int));
                }
                // All elements before k are sorted (invariant)
                // Element at k is d[j], which maintains order
                assert(forall|x: int, y: int| 0 <= x <= y < (k + 1) as int ==> 
                    b@.subrange(0, (k + 1) as int).index(x) <= b@.subrange(0, (k + 1) as int).index(y));
            };
            
            j = j + 1;
        }
        k = k + 1;
    }
    
    // Copy remaining elements from c
    while i < c.len()
        invariant
            0 <= i <= c.len(),
            j == d.len(),
            k == i + j,
            k <= b.len(),
            Sorted(b@.subrange(0, k as int)),
            multiset(b@.subrange(0, k as int)) == 
                multiset(c@.subrange(0, i as int)) + multiset(d@),
            forall|x: int| 0 <= x < k && i < c.len() ==> b@.index(x) <= c@.index(i as int),
    {
        b.set(k, c[i]);
        
        // Prove sortedness is maintained
        assert(Sorted(b@.subrange(0, (k + 1) as int))) by {
            if k > 0 {
                // Previous elements maintain order with current c[i]
                assert(b@.index(k as int - 1) <= c@.index(i as int));
            }
            // Remaining elements in c are sorted, so order is maintained
            assert(forall|x: int, y: int| 0 <= x <= y < (k + 1) as int ==> 
                b@.subrange(0, (k + 1) as int).index(x) <= b@.subrange(0, (k + 1) as int).index(y));
        };
        
        i = i + 1;
        k = k + 1;
    }
    
    // Copy remaining elements from d
    while j < d.len()
        invariant
            i == c.len(),
            0 <= j <= d.len(),
            k == i + j,
            k <= b.len(),
            Sorted(b@.subrange(0, k as int)),
            multiset(b@.subrange(0, k as int)) == 
                multiset(c@) + multiset(d@.subrange(0, j as int)),
            forall|x: int| 0 <= x < k && j < d.len() ==> b@.index(x) <= d@.index(j as int),
    {
        b.set(k, d[j]);
        
        // Prove sortedness is maintained
        assert(Sorted(b@.subrange(0, (k + 1) as int))) by {
            if k > 0 {
                // Previous elements maintain order with current d[j]
                assert(b@.index(k as int - 1) <= d@.index(j as int));
            }
            // Remaining elements in d are sorted, so order is maintained
            assert(forall|x: int, y: int| 0 <= x <= y < (k + 1) as int ==> 
                b@.subrange(0, (k + 1) as int).index(x) <= b@.subrange(0, (k + 1) as int).index(y));
        };
        
        j = j + 1;
        k = k + 1;
    }
    
    // Final assertions to help prove postconditions
    assert(k == b.len());
    assert(i == c.len() && j == d.len());
    
    // Prove that the final result equals the subrange we've been building
    assert(b@ =~= b@.subrange(0, k as int)) by {
        assert(k as int == b@.len());
        assert(b@.subrange(0, b@.len()) =~= b@);
    };
    
    // Multiset property follows from loop invariants
    assert(multiset(b@) == multiset(c@) + multiset(d@));
    
    // Final sortedness follows from the last loop invariant
    assert(Sorted(b@)) by {
        assert(b@ =~= b@.subrange(0, k as int));
        assert(Sorted(b@.subrange(0, k as int)));
    };
    
    b
}

}