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
            forall|x: int| 0 <= x < k ==> 
                (exists|y: int| 0 <= y < i && b@.index(x) == c@.index(y)) ||
                (exists|y: int| 0 <= y < j && b@.index(x) == d@.index(y)),
            multiset(b@.subrange(0, k as int)) == 
                multiset(c@.subrange(0, i as int)) + multiset(d@.subrange(0, j as int)),
            // Additional invariant to help with sortedness across loops
            forall|x: int| k > 0 && 0 <= x < i ==> b@.index((k-1) as int) <= c@.index(x),
            forall|x: int| k > 0 && 0 <= x < j ==> b@.index((k-1) as int) <= d@.index(x)
    {
        if c[i] <= d[j] {
            b.set(k, c[i]);
            assert(k > 0 ==> b@.index((k-1) as int) <= c@.index(i as int));
            assert(forall|x: int| j <= x < d.len() ==> c@.index(i as int) <= d@.index(x));
            i = i + 1;
        } else {
            b.set(k, d[j]);
            assert(k > 0 ==> b@.index((k-1) as int) <= d@.index(j as int));
            assert(forall|x: int| i <= x < c.len() ==> d@.index(j as int) <= c@.index(x));
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
            forall|x: int| k > 0 && i <= x < c.len() ==> b@.index((k-1) as int) <= c@.index(x)
    {
        b.set(k, c[i]);
        assert(k > 0 ==> b@.index((k-1) as int) <= c@.index(i as int));
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
            forall|x: int| k > 0 && j <= x < d.len() ==> b@.index((k-1) as int) <= d@.index(x)
    {
        b.set(k, d[j]);
        assert(k > 0 ==> b@.index((k-1) as int) <= d@.index(j as int));
        j = j + 1;
        k = k + 1;
    }
    
    // Final assertions to help prove the postcondition
    assert(k == b.len());
    assert(i == c.len());
    assert(j == d.len());
    assert(b@ == b@.subrange(0, k as int));
    assert(multiset(b@) == multiset(c@) + multiset(d@));
    
    b
}

}