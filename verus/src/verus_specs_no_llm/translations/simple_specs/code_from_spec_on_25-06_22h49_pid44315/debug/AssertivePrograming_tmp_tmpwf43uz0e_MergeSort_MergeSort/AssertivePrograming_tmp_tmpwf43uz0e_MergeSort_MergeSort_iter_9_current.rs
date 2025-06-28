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
            // Prove that the new element maintains sortedness
            assert(k == 0 || b@.index(k as int - 1) <= c@.index(i as int)) by {
                if k > 0 {
                    // The previous element is <= current element from c or d
                    // and we're adding the smaller of c[i] and d[j]
                }
            };
            i = i + 1;
        } else {
            b.set(k, d[j]);
            // Prove that the new element maintains sortedness
            assert(k == 0 || b@.index(k as int - 1) <= d@.index(j as int)) by {
                if k > 0 {
                    // Similar reasoning as above
                }
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
        assert(k == 0 || b@.index(k as int - 1) <= c@.index(i as int)) by {
            if k > 0 {
                // Previous elements are from sorted merge, current is next from sorted c
            }
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
        assert(k == 0 || b@.index(k as int - 1) <= d@.index(j as int)) by {
            if k > 0 {
                // Previous elements are from sorted merge, current is next from sorted d
            }
        };
        j = j + 1;
        k = k + 1;
    }
    
    // Final assertions to help prove postconditions
    assert(k == b.len());
    assert(i == c.len() && j == d.len());
    assert(b@ == b@.subrange(0, k as int));
    assert(multiset(b@) == multiset(c@) + multiset(d@));
    
    // Prove final sortedness
    assert(Sorted(b@)) by {
        assert(b@ == b@.subrange(0, k as int));
        assert(Sorted(b@.subrange(0, k as int)));
    };
    
    b
}

}