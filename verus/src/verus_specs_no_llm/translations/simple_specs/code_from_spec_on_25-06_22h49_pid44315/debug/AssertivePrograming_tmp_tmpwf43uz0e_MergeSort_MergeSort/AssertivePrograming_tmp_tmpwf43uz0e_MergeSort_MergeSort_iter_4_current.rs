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
            // Key invariant: last element in merged portion is <= remaining elements
            i < c.len() ==> (k == 0 || b@.index((k-1) as int) <= c@.index(i as int)),
            j < d.len() ==> (k == 0 || b@.index((k-1) as int) <= d@.index(j as int))
    {
        if c[i] <= d[j] {
            b.set(k, c[i]);
            
            // Proof annotations to help verification
            assert(b@.index(k as int) == c@.index(i as int));
            assert(multiset(b@.subrange(0, (k+1) as int)) == 
                   multiset(c@.subrange(0, (i+1) as int)) + multiset(d@.subrange(0, j as int)));
            
            i = i + 1;
        } else {
            b.set(k, d[j]);
            
            // Proof annotations to help verification
            assert(b@.index(k as int) == d@.index(j as int));
            assert(multiset(b@.subrange(0, (k+1) as int)) == 
                   multiset(c@.subrange(0, i as int)) + multiset(d@.subrange(0, (j+1) as int)));
            
            j = j + 1;
        }
        k = k + 1;
    }
    
    while i < c.len()
        invariant
            0 <= i <= c.len(),
            j == d.len(),
            k == i + j,
            k <= b.len(),
            Sorted(b@.subrange(0, k as int)),
            multiset(b@.subrange(0, k as int)) == 
                multiset(c@.subrange(0, i as int)) + multiset(d@),
            i < c.len() ==> (k == 0 || b@.index((k-1) as int) <= c@.index(i as int))
    {
        b.set(k, c[i]);
        
        // Proof annotation
        assert(multiset(b@.subrange(0, (k+1) as int)) == 
               multiset(c@.subrange(0, (i+1) as int)) + multiset(d@));
        
        i = i + 1;
        k = k + 1;
    }
    
    while j < d.len()
        invariant
            i == c.len(),
            0 <= j <= d.len(),
            k == i + j,
            k <= b.len(),
            Sorted(b@.subrange(0, k as int)),
            multiset(b@.subrange(0, k as int)) == 
                multiset(c@) + multiset(d@.subrange(0, j as int)),
            j < d.len() ==> (k == 0 || b@.index((k-1) as int) <= d@.index(j as int))
    {
        b.set(k, d[j]);
        
        // Proof annotation
        assert(multiset(b@.subrange(0, (k+1) as int)) == 
               multiset(c@) + multiset(d@.subrange(0, (j+1) as int)));
        
        j = j + 1;
        k = k + 1;
    }
    
    // Final assertions to help verification
    assert(k == b.len());
    assert(i == c.len());
    assert(j == d.len());
    assert(k as int == c.len() + d.len());
    
    // Prove that the final result satisfies the postconditions
    assert(b@.subrange(0, k as int) == b@);
    assert(multiset(b@) == multiset(c@) + multiset(d@));
    
    // Prove sortedness by leveraging the loop invariants and the fact that
    // we've processed all elements maintaining the sorted property
    assert(Sorted(b@.subrange(0, k as int)));
    assert(Sorted(b@));
    
    b
}

}