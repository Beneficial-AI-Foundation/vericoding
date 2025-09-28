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
spec fn inv_merge(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat) -> bool {
    inv_sorted(b, c, d, i, j) && inv_sub_set(b, c, d, i, j)
}

proof fn lemma_multiset_full<T>(s1: Seq<T>, s2: Seq<T>)
    requires
        s1.len() == s2.len(),
        s1.to_multiset() =~= s2.to_multiset(),
    ensures
        s1 =~= s2,
{
    assert(s1.to_multiset().ext_equal(s2.to_multiset()));
}

proof fn lemma_multiset_prefix_add_one(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat, k: bool)
    requires
        i < c.len(),
        j <= d.len(),
        inv_sub_set(b, c, d, i,
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
spec fn inv_merge(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat) -> bool {
    inv_sorted(b, c, d, i, j) && inv_sub_set(b, c, d, i, j)
}

proof fn lemma_multiset_full<T>(s1: Seq<T>, s2: Seq<T>)
    requires
        s1.len() == s2.len(),
        s1.to_multiset() =~= s2.to_multiset(),
    ensures
        s1 =~= s2,
{
    assert(s1.to_multiset().ext_equal(s2.to_multiset()));
}

proof fn lemma_multiset_prefix_add_one(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat, k: bool)
    requires
        i < c.len(),
        j <= d.len(),
        inv_sub_set(b, c, d, i,
// </vc-code>

fn main() {}

}