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
                multiset(c@.subrange(0, i as int)) + multiset(d@.subrange(0, j as int))
    {
        if c[i] <= d[j] {
            b.set(k, c[i]);
            i = i + 1;
        } else {
            b.set(k, d[j]);
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
                multiset(c@.subrange(0, i as int)) + multiset(d@)
    {
        b.set(k, c[i]);
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
                multiset(c@) + multiset(d@.subrange(0, j as int))
    {
        b.set(k, d[j]);
        j = j + 1;
        k = k + 1;
    }
    
    b
}

}