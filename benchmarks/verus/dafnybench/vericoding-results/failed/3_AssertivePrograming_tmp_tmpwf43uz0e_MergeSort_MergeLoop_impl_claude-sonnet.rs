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
    b.subrange(0, (i + j) as int).to_multiset() =~= 
    c.subrange(0, i as int).to_multiset().add(d.subrange(0, j as int).to_multiset())
}

//This lemma helps dafny see that if the prefixs of arrays are the same multiset until the end of the arrays,
//all the arrays are the same multiset.


//This lemma helps dafny see that after adding the next value from c to b the prefixes are still the same subsets.

// <vc-helpers>
proof fn lemma_inv_sorted_step_c(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat)
    requires
        i < c.len(),
        j <= d.len(),
        i + j < b.len(),
        sorted(c),
        sorted(d),
        inv_sorted(b, c, d, i, j),
        j >= d.len() || c[i as int] <= d[j as int],
    ensures
        inv_sorted(b.update((i + j) as int, c[i as int]), c, d, i + 1, j),
{
    let new_b = b.update((i + j) as int, c[i as int]);
    let new_i = i + 1;
    let new_j = j;
    
    // Prove sortedness by showing all pairs are in order
    assert forall|k1: int, k2: int| 0 <= k1 <= k2 < (new_i + new_j) as int
        implies new_b[k1] <= new_b[k2] by {
        if k2 < (i + j) as int {
            // Both indices are in the old sorted part
            assert(new_b[k1] == b[k1]);
            assert(new_b[k2] == b[k2]);
        } else if k1 < (i + j) as int && k2 == (i + j) as int {
            // k1 is in old part, k2 is the new element
            assert(new_b[k1] == b[k1]);
            assert(new_b[k2] == c[i as int]);
            if i + j > 0 {
                if k1 <= (i + j - 1) as int {
                    // Use transitivity through the last element
                    assert(b[k1] <= b[(i + j - 1) as int]);
                    assert(b[(i + j - 1) as int] <= c[i as int]);
                }
            }
        } else {
            // k1 == k2 == (i + j) as int
            assert(k1 == k2);
        }
    };
}

proof fn lemma_inv_sorted_step_d(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat)
    requires
        i <= c.len(),
        j < d.len(),
        i + j < b.len(),
        sorted(c),
        sorted(d),
        inv_sorted(b, c, d, i, j),
        i >= c.len() || d[j as int] < c[i as int],
    ensures
        inv_sorted(b.update((i + j) as int, d[j as int]), c, d, i, j + 1),
{
    let new_b = b.update((i + j) as int, d[j as int]);
    let new_i = i;
    let new_j = j + 1;
    
    // Prove sortedness by showing all pairs are in order
    assert forall|k1: int, k2: int| 0 <= k1 <= k2 < (new_i + new_j) as int
        implies new_b[k1] <= new_b[k2] by {
        if k2 < (i + j) as int {
            // Both indices are in the old sorted part
            assert(new_b[k1] == b[k1]);
            assert(new_b[k2] == b[k2]);
        } else if k1 < (i + j) as int && k2 == (i + j) as int {
            // k1 is in old part, k2 is the new element
            assert(new_b[k1] == b[k1]);
            assert(new_b[k2] == d[j as int]);
            if i + j > 0 {
                if k1 <= (i + j - 1) as int {
                    // Use transitivity through the last element
                    assert(b[k1] <= b[(i + j - 1) as int]);
                    assert(b[(i + j - 1) as int] <= d[j as int]);
                }
            }
        } else {
            // k1 == k2 == (i + j) as int
            assert(k1 == k2);
        }
    };
}

proof fn lemma_inv_subset_step_c(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat)
    requires
        i < c.len(),
        j <= d.len(),
        i + j < b.len(),
        inv_sub_set(b, c, d, i, j),
    ensures
        inv_sub_set(b.update((i + j) as int, c[i as int]), c, d, i + 1, j),
{
    let new_b = b.update((i + j) as int, c[i as int]);
    let new_i = i + 1;
    let new_j = j;
    
    // Key insight: the update extends the prefix by one element
    assert(new_b.subrange(0, (new_i + new_j) as int) =~= 
           b.subrange(0, (i + j) as int) + seq![c[i as int]]);
    
    // The c subrange is extended by one element
    assert(c.subrange(0, new_i as int) =~= 
           c.subrange(0, i as int) + seq![c[i as int]]);
    
    // The d subrange stays the same
    assert(d.subrange(0, new_j as int) =~= d.subrange(0, j as int));
    
    // Use the existing invariant and multiset properties
    assert(b.subrange(0, (i + j) as int).to_multiset() =~= 
           c.subrange(0, i as int).to_multiset().add(d.subrange(0, j as int).to_multiset()));
}

proof fn lemma_inv_subset_step_d(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat)
    requires
        i <= c.len(),
        j < d.len(),
        i + j < b.len(),
        inv_sub_set(b, c, d, i, j),
    ensures
        inv_sub_set(b.update((i + j) as int, d[j as int]), c, d, i, j + 1),
{
    let new_b = b.update((i + j) as int, d[j as int]);
    let new_i = i;
    let new_j = j + 1;
    
    // Key insight: the update extends the prefix by one element
    assert(new_b.subrange(0, (new_i + new_j) as int) =~= 
           b.subrange(0, (i + j) as int) + seq![d[j as int]]);
    
    // The c subrange stays the same
    assert(c.subrange(0, new_i as int) =~= c.subrange(0, i as int));
    
    // The d subrange is extended by one element
    assert(d.subrange(0, new_j as int) =~= 
           d.subrange(0, j as int) + seq![d[j as int]]);
    
    // Use the existing invariant and multiset properties
    assert(b.subrange(0, (i + j) as int).to_multiset() =~= 
           c.subrange(0, i as int).to_multiset().add(d.subrange(0, j as int).to_multiset()));
}
// </vc-helpers>

// <vc-spec>
fn merge_loop(b: &mut Vec<int>, c: &Vec<int>, d: &Vec<int>, i0: usize, j0: usize) -> (r: (usize, usize))
        requires
            old(b).len() == c.len() + d.len(),
            sorted(c@),
            sorted(d@),
            i0 <= c.len(),
            j0 <= d.len(),
            i0 + j0 <= old(b).len(),
            inv_sub_set(old(b)@, c@, d@, i0 as nat, j0 as nat),
            inv_sorted(old(b)@, c@, d@, i0 as nat, j0 as nat),
            i0 + j0 < old(b).len(),

        ensures
            r.0 <= c.len() && r.1 <= d.len() && r.0 + r.1 <= b.len(),
            inv_sub_set(b@, c@, d@, r.0 as nat, r.1 as nat),
            inv_sorted(b@, c@, d@, r.0 as nat, r.1 as nat),
            //decreases ensures
            0 <= c.len() - r.0 < c.len() - i0 || (c.len() - r.0 == c.len() - i0 && 0 <= d.len() - r.1 < d.len() - j0)
// </vc-spec>
// <vc-code>
{
    let mut i = i0;
    let mut j = j0;
    
    if i >= c.len() {
        // Must take from d
        b.set(i + j, d[j]);
        proof {
            lemma_inv_subset_step_d(old(b)@, c@, d@, i as nat, j as nat);
            lemma_inv_sorted_step_d(old(b)@, c@, d@, i as nat, j as nat);
        }
        j += 1;
    } else if j >= d.len() {
        // Must take from c
        b.set(i + j, c[i]);
        proof {
            lemma_inv_subset_step_c(old(b)@, c@, d@, i as nat, j as nat);
            lemma_inv_sorted_step_c(old(b)@, c@, d@, i as nat, j as nat);
        }
        i += 1;
    } else if c[i] <= d[j] {
        // Take from c
        b.set(i + j, c[i]);
        proof {
            lemma_inv_subset_step_c(old(b)@, c@, d@, i as nat, j as nat);
            lemma_inv_sorted_step_c(old(b)@, c@, d@, i as nat, j as nat);
        }
        i += 1;
    } else {
        // Take from d
        b.set(i + j, d[j]);
        proof {
            lemma_inv_subset_step_d(old(b)@, c@, d@, i as nat, j as nat);
            lemma_inv_sorted_step_d(old(b)@, c@, d@, i as nat, j as nat);
        }
        j += 1;
    }
    
    (i, j)
}
// </vc-code>

fn main() {
}

}