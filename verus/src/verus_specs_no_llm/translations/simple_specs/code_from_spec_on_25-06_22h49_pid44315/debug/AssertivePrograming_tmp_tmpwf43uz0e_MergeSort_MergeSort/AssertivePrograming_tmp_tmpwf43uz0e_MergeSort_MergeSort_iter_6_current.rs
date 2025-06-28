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
            j < d.len() ==> (k == 0 || b@.index((k-1) as int) <= d@.index(j as int)),
            // Additional invariants for sortedness preservation
            forall|x: int| 0 <= x < k ==> 
                (i < c.len() ==> b@.index(x) <= c@.index(i as int)) &&
                (j < d.len() ==> b@.index(x) <= d@.index(j as int))
    {
        if c[i] <= d[j] {
            // Prove that adding c[i] maintains sortedness
            assert(k == 0 || b@.index((k-1) as int) <= c@.index(i as int));
            assert(forall|x: int| 0 <= x < k ==> b@.index(x) <= c@.index(i as int));
            
            b.set(k, c[i]);
            
            // Help prove the updated sequence is sorted
            assert(forall|x: int, y: int| 0 <= x <= y <= k ==> b@.index(x) <= b@.index(y));
            
            i = i + 1;
        } else {
            // Prove that adding d[j] maintains sortedness
            assert(k == 0 || b@.index((k-1) as int) <= d@.index(j as int));
            assert(forall|x: int| 0 <= x < k ==> b@.index(x) <= d@.index(j as int));
            
            b.set(k, d[j]);
            
            // Help prove the updated sequence is sorted
            assert(forall|x: int, y: int| 0 <= x <= y <= k ==> b@.index(x) <= b@.index(y));
            
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
            i < c.len() ==> (k == 0 || b@.index((k-1) as int) <= c@.index(i as int)),
            forall|x: int| 0 <= x < k ==> 
                (i < c.len() ==> b@.index(x) <= c@.index(i as int))
    {
        assert(k == 0 || b@.index((k-1) as int) <= c@.index(i as int));
        assert(forall|x: int| 0 <= x < k ==> b@.index(x) <= c@.index(i as int));
        
        b.set(k, c[i]);
        
        assert(forall|x: int, y: int| 0 <= x <= y <= k ==> b@.index(x) <= b@.index(y));
        
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
            j < d.len() ==> (k == 0 || b@.index((k-1) as int) <= d@.index(j as int)),
            forall|x: int| 0 <= x < k ==> 
                (j < d.len() ==> b@.index(x) <= d@.index(j as int))
    {
        assert(k == 0 || b@.index((k-1) as int) <= d@.index(j as int));
        assert(forall|x: int| 0 <= x < k ==> b@.index(x) <= d@.index(j as int));
        
        b.set(k, d[j]);
        
        assert(forall|x: int, y: int| 0 <= x <= y <= k ==> b@.index(x) <= b@.index(y));
        
        j = j + 1;
        k = k + 1;
    }
    
    // Final assertions to help prove postconditions
    assert(k == c.len() + d.len());
    assert(i == c.len() && j == d.len());
    assert(multiset(b@) == multiset(c@) + multiset(d@));
    assert(Sorted(b@));
    
    b
}

}