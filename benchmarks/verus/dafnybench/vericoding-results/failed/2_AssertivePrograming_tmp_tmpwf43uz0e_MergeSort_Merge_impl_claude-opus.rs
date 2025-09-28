use vstd::prelude::*;

verus! {

// Noa Leron 207131871
// Tsuri Farhana 315016907




spec fn sorted(q: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < q.len() ==> q[i] <= q[j]
}

/*
Goal: Implement the well known merge sort algorithm in O(a.Length X log_2(a.Length)) time, recursively.

- Divide the contents of the original array into two local arrays
- After sorting the local arrays (recursively), merge the contents of the two returned arrays using the Merge method (see below)
- DO NOT modify the specification or any other part of the method's signature
- DO NOT introduce any further methods
*/

spec fn inv(a: Seq<i32>, a1: Seq<i32>, a2: Seq<i32>, i: usize, mid: usize) -> bool {
    (i <= a1.len()) && (i <= a2.len()) && (i + mid <= a.len()) &&
    (a1.subrange(0, i as int) == a.subrange(0, i as int)) && 
    (a2.subrange(0, i as int) == a.subrange(mid as int, (i + mid) as int))
}


/*
Goal: Implement iteratively, correctly, efficiently, clearly

DO NOT modify the specification or any other part of the method's signature
*/

//This is a method that replace the loop body
fn merge_loop(b: &mut Vec<i32>, c: &Vec<i32>, d: &Vec<i32>, i0: usize, j0: usize) -> (usize, usize)
        requires
            old(b).len() == c.len() + d.len(),
            sorted(c@),
            sorted(d@),
            i0 <= c.len(),
            j0 <= d.len(),
            i0 + j0 <= old(b).len(),
            inv_sub_set(old(b)@, c@, d@, i0, j0),
            inv_sorted(old(b)@, c@, d@, i0, j0),
            i0 + j0 < old(b).len(),
{
    let mut i = i0;
    let mut j = j0;

    if i == c.len() || (j < d.len() && d[j] < c[i]) {
        // in this case we take the next value from d
        b.set(i + j, d[j]);
        j = j + 1;
    } else {
        // in this case we take the next value from c
        b.set(i + j, c[i]);
        i = i + 1;
    }

    (i, j)
}


//Loop invariant - b is sorted so far and the next two potential values that will go into b are bigger than the biggest value in b.
spec fn inv_sorted(b: Seq<i32>, c: Seq<i32>, d: Seq<i32>, i: usize, j: usize) -> bool {
    i <= c.len() && j <= d.len() && i + j <= b.len() &&
    ((i + j > 0 && i < c.len()) ==> (b[j + i - 1] <= c[i as int])) &&
    ((i + j > 0 && j < d.len()) ==> (b[j + i - 1] <= d[j as int])) &&
    sorted(b.subrange(0, (i + j) as int))
}


//Loop invariant - the multiset of the prefix of b so far is the same multiset as the prefixes of c and d so far.
spec fn inv_sub_set(b: Seq<i32>, c: Seq<i32>, d: Seq<i32>, i: usize, j: usize) -> bool {
    i <= c.len() && j <= d.len() && i + j <= b.len() &&
    b.subrange(0, (i + j) as int).to_multiset() == 
        c.subrange(0, i as int).to_multiset().add(d.subrange(0, j as int).to_multiset())
}

//This lemma helps Verus see that if the prefixes of arrays are the same multiset until the end of the arrays,
//all the arrays are the same multiset.


//This lemma helps Verus see that after adding the next value from c to b the prefixes are still the same subsets.

// <vc-helpers>
use vstd::multiset::Multiset;

proof fn lemma_inv_sub_set_maintained_c(b: Seq<i32>, c: Seq<i32>, d: Seq<i32>, i: usize, j: usize)
    requires
        i < c.len(),
        j <= d.len(),
        i + j < b.len(),
        inv_sub_set(b, c, d, i, j),
        b.len() == c.len() + d.len(),
    ensures
        i + 1 <= c.len(),
        j <= d.len(),
        (i + 1) + j <= b.len(),
        inv_sub_set(b.update((i + j) as int, c[i as int]), c, d, i + 1, j),
{
    let b_new = b.update((i + j) as int, c[i as int]);
    assert((i + 1) + j == i + j + 1);
    assert(b_new.subrange(0, ((i + 1) + j) as int) =~= 
           b_new.subrange(0, (i + j) as int).push(b_new[(i + j) as int]));
    assert(b_new.subrange(0, (i + j) as int) =~= b.subrange(0, (i + j) as int));
    assert(c.subrange(0, (i + 1) as int) =~= c.subrange(0, i as int).push(c[i as int]));
}

proof fn lemma_inv_sub_set_maintained_d(b: Seq<i32>, c: Seq<i32>, d: Seq<i32>, i: usize, j: usize)
    requires
        i <= c.len(),
        j < d.len(),
        i + j < b.len(),
        inv_sub_set(b, c, d, i, j),
        b.len() == c.len() + d.len(),
    ensures
        i <= c.len(),
        j + 1 <= d.len(),
        i + (j + 1) <= b.len(),
        inv_sub_set(b.update((i + j) as int, d[j as int]), c, d, i, j + 1),
{
    let b_new = b.update((i + j) as int, d[j as int]);
    assert(i + (j + 1) == i + j + 1);
    assert(b_new.subrange(0, (i + (j + 1)) as int) =~= 
           b_new.subrange(0, (i + j) as int).push(b_new[(i + j) as int]));
    assert(b_new.subrange(0, (i + j) as int) =~= b.subrange(0, (i + j) as int));
    assert(d.subrange(0, (j + 1) as int) =~= d.subrange(0, j as int).push(d[j as int]));
}

proof fn lemma_final_multiset(b: Seq<i32>, c: Seq<i32>, d: Seq<i32>)
    requires
        b.len() == c.len() + d.len(),
        c.len() <= c.len(),
        d.len() <= d.len(),
        c.len() + d.len() <= b.len(),
        inv_sub_set(b, c, d, c.len(), d.len()),
    ensures
        b.to_multiset() == c.to_multiset().add(d.to_multiset()),
{
    assert(b.subrange(0, b.len() as int) =~= b);
    assert(c.subrange(0, c.len() as int) =~= c);
    assert(d.subrange(0, d.len() as int) =~= d);
    assert((c.len() + d.len()) as int == b.len() as int);
}

proof fn lemma_inv_sorted_final(b: Seq<i32>, c: Seq<i32>, d: Seq<i32>)
    requires
        b.len() == c.len() + d.len(),
        sorted(c),
        sorted(d),
        c.len() <= c.len(),
        d.len() <= d.len(),
        c.len() + d.len() <= b.len(),
        inv_sorted(b, c, d, c.len(), d.len()),
    ensures
        sorted(b),
{
    assert(c.len() + d.len() == b.len());
    assert(b.subrange(0, b.len() as int) =~= b);
}

proof fn lemma_initial_inv_sub_set(b: Seq<i32>, c: Seq<i32>, d: Seq<i32>)
    requires
        b.len() == c.len() + d.len(),
    ensures
        inv_sub_set(b, c, d, 0, 0),
{
    assert(b.subrange(0, 0) =~= Seq::<i32>::empty());
    assert(c.subrange(0, 0) =~= Seq::<i32>::empty());
    assert(d.subrange(0, 0) =~= Seq::<i32>::empty());
    assert(Seq::<i32>::empty().to_multiset() == Multiset::<i32>::empty());
}

proof fn lemma_initial_inv_sorted(b: Seq<i32>, c: Seq<i32>, d: Seq<i32>)
    requires
        b.len() == c.len() + d.len(),
        sorted(c),
        sorted(d),
    ensures
        inv_sorted(b, c, d, 0, 0),
{
    assert(sorted(b.subrange(0, 0)));
}
// </vc-helpers>

// <vc-spec>
fn merge(b: &mut Vec<i32>, c: &Vec<i32>, d: &Vec<i32>)
    requires
        old(b).len() == c.len() + d.len(),
        sorted(c@),
        sorted(d@),
    ensures
        sorted(b@),
        b@.to_multiset() == c@.to_multiset().add(d@.to_multiset()),
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut j: usize = 0;
    
    proof {
        lemma_initial_inv_sub_set(b@, c@, d@);
        lemma_initial_inv_sorted(b@, c@, d@);
    }
    
    while i + j < b.len()
        invariant
            b.len() == c.len() + d.len(),
            sorted(c@),
            sorted(d@),
            i <= c.len(),
            j <= d.len(),
            inv_sub_set(b@, c@, d@, i, j),
            inv_sorted(b@, c@, d@, i, j),
        decreases b.len() - (i + j),
    {
        proof {
            if i == c.len() || (j < d.len() && d@[j as int] < c@[i as int]) {
                lemma_inv_sub_set_maintained_d(b@, c@, d@, i, j);
            } else {
                lemma_inv_sub_set_maintained_c(b@, c@, d@, i, j);
            }
        }
        
        let (new_i, new_j) = merge_loop(b, c, d, i, j);
        i = new_i;
        j = new_j;
    }
    
    assert(i == c.len());
    assert(j == d.len());
    
    proof {
        lemma_final_multiset(b@, c@, d@);
        lemma_inv_sorted_final(b@, c@, d@);
    }
}
// </vc-code>

fn main() {}

}