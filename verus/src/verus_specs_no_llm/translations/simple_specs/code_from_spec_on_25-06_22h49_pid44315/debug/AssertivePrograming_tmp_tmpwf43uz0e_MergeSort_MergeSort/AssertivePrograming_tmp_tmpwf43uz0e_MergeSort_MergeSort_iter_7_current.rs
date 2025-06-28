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
            // Monotonicity: elements in b are <= remaining elements in c and d
            forall|x: int| 0 <= x < k && i < c.len() ==> b@.index(x) <= c@.index(i as int),
            forall|x: int| 0 <= x < k && j < d.len() ==> b@.index(x) <= d@.index(j as int),
            // Sorted property of remaining elements
            Sorted(c@.subrange(i as int, c.len() as int)),
            Sorted(d@.subrange(j as int, d.len() as int)),
    {
        if c[i] <= d[j] {
            b.set(k, c[i]);
            
            // Prove sortedness is maintained
            assert(forall|x: int| 0 <= x < k ==> b@.index(x) <= c@.index(i as int));
            assert(forall|x: int| 0 <= x < k ==> b@.index(x) <= b@.index(k as int));
            assert(Sorted(b@.subrange(0, (k+1) as int)));
            
            // Prove multiset property
            assert(multiset(b@.subrange(0, (k+1) as int)) == 
                   multiset(c@.subrange(0, (i+1) as int)) + multiset(d@.subrange(0, j as int)));
            
            i = i + 1;
        } else {
            b.set(k, d[j]);
            
            // Prove sortedness is maintained
            assert(forall|x: int| 0 <= x < k ==> b@.index(x) <= d@.index(j as int));
            assert(forall|x: int| 0 <= x < k ==> b@.index(x) <= b@.index(k as int));
            assert(Sorted(b@.subrange(0, (k+1) as int)));
            
            // Prove multiset property
            assert(multiset(b@.subrange(0, (k+1) as int)) == 
                   multiset(c@.subrange(0, i as int)) + multiset(d@.subrange(0, (j+1) as int)));
            
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
            Sorted(c@.subrange(i as int, c.len() as int)),
    {
        b.set(k, c[i]);
        
        // Prove sortedness is maintained
        assert(forall|x: int| 0 <= x < k ==> b@.index(x) <= c@.index(i as int));
        assert(forall|x: int| 0 <= x < k ==> b@.index(x) <= b@.index(k as int));
        assert(Sorted(b@.subrange(0, (k+1) as int)));
        
        // Prove multiset property
        assert(multiset(b@.subrange(0, (k+1) as int)) == 
               multiset(c@.subrange(0, (i+1) as int)) + multiset(d@));
        
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
            Sorted(d@.subrange(j as int, d.len() as int)),
    {
        b.set(k, d[j]);
        
        // Prove sortedness is maintained
        assert(forall|x: int| 0 <= x < k ==> b@.index(x) <= d@.index(j as int));
        assert(forall|x: int| 0 <= x < k ==> b@.index(x) <= b@.index(k as int));
        assert(Sorted(b@.subrange(0, (k+1) as int)));
        
        // Prove multiset property
        assert(multiset(b@.subrange(0, (k+1) as int)) == 
               multiset(c@) + multiset(d@.subrange(0, (j+1) as int)));
        
        j = j + 1;
        k = k + 1;
    }
    
    // Final proof that we've merged everything correctly
    assert(k == c.len() + d.len());
    assert(i == c.len() && j == d.len());
    assert(b@.subrange(0, k as int) == b@);
    assert(c@.subrange(0, i as int) == c@);
    assert(d@.subrange(0, j as int) == d@);
    assert(multiset(b@) == multiset(c@) + multiset(d@));
    assert(Sorted(b@));
    
    b
}

}