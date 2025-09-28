use vstd::prelude::*;

verus! {

// Noa Leron 207131871
// Tsuri Farhana 315016907



spec fn sorted(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < q.len() ==> q[i] <= q[j]
}

/*
Goal: Implement the well known merge sort algorithm in O(a.Length X log_2(a.Length)) time, recursively.

- Divide the contents of the original array into two local arrays
- After sorting the local arrays (recursively), merge the contents of the two returned arrays using the Merge method (see below)
- DO NOT modify the specification or any other part of the method's signature
- DO NOT introduce any further methods
*/

spec fn inv(a: Seq<int>, a1: Seq<int>, a2: Seq<int>, i: nat, mid: nat) -> bool {
    (i <= a1.len()) && (i <= a2.len()) && (i + mid <= a.len()) &&
    (a1.subrange(0, i as int) =~= a.subrange(0, i as int)) && 
    (a2.subrange(0, i as int) =~= a.subrange(mid as int, (i + mid) as int))
}

/*
Goal: Implement iteratively, correctly, efficiently, clearly

DO NOT modify the specification or any other part of the method's signature
*/
fn merge(b: &mut Vec<int>, c: &Vec<int>, d: &Vec<int>)
    requires
        old(b).len() == c.len() + d.len(),
        sorted(c@),
        sorted(d@),
    ensures
        sorted(b@),
        b@.to_multiset() == c@.to_multiset().add(d@.to_multiset()),
{
  assume(false);
}


//This is a method that replace the loop body


//Loop invariant - b is sorted so far and the next two potential values that will go into b are bigger then the biggest value in b.
spec fn inv_sorted(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat) -> bool {
    i <= c.len() && j <= d.len() && i + j <= b.len() &&
    ((i + j > 0 && i < c.len()) ==> (b[(j + i - 1) as int] <= c[i as int])) &&
    ((i + j > 0 && j < d.len()) ==> (b[(j + i - 1) as int] <= d[j as int])) &&
    sorted(b.subrange(0, (i + j) as int))
    }


//Loop invariant - the multiset of the prefix of b so far is the same multiset as the prefixes of c and d so far.
spec fn inv_sub_set(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat) -> bool {
    i <= c.len() && j <= d.len() && i + j <= b.len() &&
    b.subrange(0, (i + j) as int).to_multiset() == 
        c.subrange(0, i as int).to_multiset().add(d.subrange(0, j as int).to_multiset())
}

//This lemma helps verus see that if the prefixes of arrays are the same multiset until the end of the arrays,
//all the arrays are the same multiset.


//This lemma helps verus see that after adding the next value from c to b the prefixes are still the same subsets.

// <vc-helpers>
proof fn lemma_multiset_full_arrays(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat)
    requires
        i == c.len(),
        j == d.len(),
        inv_sub_set(b, c, d, i, j),
    ensures
        b.to_multiset() == c.to_multiset().add(d.to_multiset()),
{
    assert(c.subrange(0, i as int) =~= c);
    assert(d.subrange(0, j as int) =~= d);
    assert(b.subrange(0, (i + j) as int) =~= b);
}

proof fn lemma_add_from_c_multiset(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat, new_b: Seq<int>)
    requires
        inv_sub_set(b, c, d, i, j),
        i < c.len(),
        new_b == b.update((i + j) as int, c[i as int]),
    ensures
        inv_sub_set(new_b, c, d, i + 1, j),
{
    assert(new_b.subrange(0, (i + j + 1) as int) =~= 
           b.subrange(0, (i + j) as int).push(c[i as int]));
    assert(c.subrange(0, (i + 1) as int) =~= 
           c.subrange(0, i as int).push(c[i as int]));
}

proof fn lemma_add_from_d_multiset(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat, new_b: Seq<int>)
    requires
        inv_sub_set(b, c, d, i, j),
        j < d.len(),
        new_b == b.update((i + j) as int, d[j as int]),
    ensures
        inv_sub_set(new_b, c, d, i, j + 1),
{
    assert(new_b.subrange(0, (i + j + 1) as int) =~= 
           b.subrange(0, (i + j) as int).push(d[j as int]));
    assert(d.subrange(0, (j + 1) as int) =~= 
           d.subrange(0, j as int).push(d[j as int]));
}

proof fn lemma_multiset_conservation(a: Seq<int>, a1: Seq<int>, a2: Seq<int>, mid: nat)
    requires
        mid <= a.len(),
        a1 =~= a.subrange(0, mid as int),
        a2 =~= a.subrange(mid as int, a.len() as int),
    ensures
        a1.to_multiset().add(a2.to_multiset()) == a.to_multiset(),
{
    assert(a =~= a1 + a2);
}
// </vc-helpers>

// <vc-spec>
fn merge_sort(a: Vec<int>) -> (b: Vec<int>)
    ensures
        b.len() == a.len(),
        sorted(b@),
        a@.to_multiset() == b@.to_multiset(),
    decreases a.len()
// </vc-spec>
// <vc-code>
{
    if a.len() <= 1 {
        return a;
    }
    
    let mid = a.len() / 2;
    
    let mut a1: Vec<int> = Vec::new();
    let mut a2: Vec<int> = Vec::new();
    
    for i in 0..mid
        invariant
            i <= mid,
            a1.len() == i,
            forall|k: int| 0 <= k < i ==> a1@[k] == a@[k],
    {
        a1.push(a[i]);
    }
    
    for i in mid..a.len()
        invariant
            mid <= i <= a.len(),
            a2.len() == i - mid,
            forall|k: int| 0 <= k < (i - mid) ==> a2@[k] == a@[mid + k],
    {
        a2.push(a[i]);
    }
    
    let b1 = merge_sort(a1);
    let b2 = merge_sort(a2);
    
    let mut result: Vec<int> = Vec::with_capacity(a.len());
    for _ in 0..a.len() {
        result.push(0);
    }
    
    merge(&mut result, &b1, &b2);
    
    proof {
        lemma_multiset_conservation(a@, a1@, a2@, mid as nat);
        assert(b1@.to_multiset().add(b2@.to_multiset()) == a@.to_multiset());
    }
    
    result
}
// </vc-code>

fn main() {}

}