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
// Helper lemma to prove that adding one element maintains the multiset invariant
proof fn lemma_multiset_step_c(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat)
    requires
        i < c.len(),
        j <= d.len(),
        i + j < b.len(),
        b.subrange(0, (i + j) as int).to_multiset() =~= 
            c.subrange(0, i as int).to_multiset().add(d.subrange(0, j as int).to_multiset()),
        b[(i + j) as int] == c[i as int],
    ensures
        b.subrange(0, (i + j + 1) as int).to_multiset() =~= 
            c.subrange(0, (i + 1) as int).to_multiset().add(d.subrange(0, j as int).to_multiset()),
{
    // The key insight: subrange(0, n+1) includes element at index n
    assert(b.subrange(0, (i + j + 1) as int).to_multiset() =~=
           b.subrange(0, (i + j) as int).to_multiset().insert(b[(i + j) as int]));
    
    assert(c.subrange(0, (i + 1) as int).to_multiset() =~=
           c.subrange(0, i as int).to_multiset().insert(c[i as int]));
    
    // Since b[(i + j) as int] == c[i as int], the multisets match
}

proof fn lemma_multiset_step_d(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat)
    requires
        i <= c.len(),
        j < d.len(),
        i + j < b.len(),
        b.subrange(0, (i + j) as int).to_multiset() =~= 
            c.subrange(0, i as int).to_multiset().add(d.subrange(0, j as int).to_multiset()),
        b[(i + j) as int] == d[j as int],
    ensures
        b.subrange(0, (i + j + 1) as int).to_multiset() =~= 
            c.subrange(0, i as int).to_multiset().add(d.subrange(0, (j + 1) as int).to_multiset()),
{
    // The key insight: subrange(0, n+1) includes element at index n
    assert(b.subrange(0, (i + j + 1) as int).to_multiset() =~=
           b.subrange(0, (i + j) as int).to_multiset().insert(b[(i + j) as int]));
    
    assert(d.subrange(0, (j + 1) as int).to_multiset() =~=
           d.subrange(0, j as int).to_multiset().insert(d[j as int]));
    
    // Since b[(i + j) as int] == d[j as int], the multisets match
}

// Helper lemma to prove sorted property is maintained
proof fn lemma_sorted_step(b: Seq<int>, i: nat, j: nat, val: int)
    requires
        i + j < b.len(),
        sorted(b.subrange(0, (i + j) as int)),
        i + j > 0 ==> b[(i + j - 1) as int] <= val,
        b[(i + j) as int] == val,
    ensures
        sorted(b.subrange(0, (i + j + 1) as int)),
{
    assert forall|k: int, l: int| 0 <= k <= l < (i + j + 1) implies b[k] <= b[l] by {
        if l == (i + j) as int {
            // l is the newly added element
            if k == l {
                // b[k] == b[l] == val
            } else {
                // k < i + j
                if i + j == 0 {
                    // Impossible since k >= 0 and k < i + j = 0
                    assert(false);
                } else {
                    // i + j > 0
                    if k == (i + j - 1) as int {
                        // Direct from precondition
                        assert(b[k] <= val);
                        assert(b[l] == val);
                    } else {
                        // k < i + j - 1
                        // From sorted precondition
                        assert(0 <= k <= (i + j - 1) < (i + j));
                        assert(b[k] <= b[(i + j - 1) as int]);
                        assert(b[(i + j - 1) as int] <= val);
                        assert(b[l] == val);
                    }
                }
            }
        } else {
            // Both k and l are in the already sorted portion
            assert(l < (i + j) as int);
            // From sorted precondition
        }
    }
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
    
    if i < c.len() && (j >= d.len() || c[i] <= d[j]) {
        // Take from c
        let old_b = b@;
        b[i + j] = c[i];
        
        proof {
            // The array b only changed at position i + j
            assert(forall|k: int| 0 <= k < b.len() && k != (i + j) as int ==> b[k] == old_b[k]);
            
            // Prove sorted invariant is maintained
            if i + j > 0 {
                assert(inv_sorted(old_b, c@, d@, i as nat, j as nat));
                assert(old_b[(i + j - 1) as int] <= c[i as int]);
            }
            
            // Prove the multiset invariant
            assert(old_b.subrange(0, (i + j) as int) =~= b@.subrange(0, (i + j) as int));
            assert(b[(i + j) as int] == c[i as int]);
            
            lemma_multiset_step_c(b@, c@, d@, i as nat, j as nat);
            lemma_sorted_step(b@, i as nat, j as nat, c[i as int]);
            
            // Prove inv_sorted for the new state
            assert(i + 1 <= c.len());
            assert(j <= d.len());
            assert((i + 1) + j <= b.len());
            
            if i + 1 < c.len() && (i + 1) + j > 0 {
                assert(b[((i + 1) + j - 1) as int] == c[i as int]);
                assert(sorted(c@));
                assert(c[i as int] <= c[(i + 1) as int]);
                assert(b[((i + 1) + j - 1) as int] <= c[(i + 1) as int]);
            }
            
            if j < d.len() && (i + 1) + j > 0 {
                assert(b[((i + 1) + j - 1) as int] == c[i as int]);
                if j >= d.len() || c[i as int] <= d[j as int] {
                    assert(c[i as int] <= d[j as int]);
                }
                assert(b[((i + 1) + j - 1) as int] <= d[j as int]);
            }
        }
        
        i = i + 1;
    } else {
        // Take from d
        let old_b = b@;
        b[i + j] = d[j];
        
        proof {
            // The array b only changed at position i + j
            assert(forall|k: int| 0 <= k < b.len() && k != (i + j) as int ==> b[k] == old_b[k]);
            
            // Prove sorted invariant is maintained
            if i + j > 0 {
                assert(inv_sorted(old_b, c@, d@, i as nat, j as nat));
                assert(old_b[(i + j - 1) as int] <= d[j as int]);
            }
            
            // Prove the multiset invariant
            assert(old_b.subrange(0, (i + j) as int) =~= b@.subrange(0, (i + j) as int));
            assert(b[(i + j) as int] == d[j as int]);
            
            lemma_multiset_step_d(b@, c@, d@, i as nat, j as nat);
            lemma_sorted_step(b@, i as nat, j as nat, d[j as int]);
            
            // Prove inv_sorted for the new state
            assert(i <= c.len());
            assert(j + 1 <= d.len());
            assert(i + (j + 1) <= b.len());
            
            if i < c.len() && i + (j + 1) > 0 {
                assert(b[(i + (j + 1) - 1) as int] == d[j as int]);
                if !(i < c.len() && (j >= d.len() || c[i as int] <= d[j as int])) {
                    assert(j < d.len());
                    assert(d[j as int] < c[i as int] || (j < d.len() && c[i as int] > d[j as int]));
                    assert(d[j as int] < c[i as int]);
                }
                assert(b[(i + (j + 1) - 1) as int] <= c[i as int]);
            }
            
            if j + 1 < d.len() && i + (j + 1) > 0 {
                assert(b[(i + (j + 1) - 1) as int] == d[j as int]);
                assert(sorted(d@));
                assert(d[j as int] <= d[(j + 1) as int]);
                assert(b[(i + (j + 1) - 1) as int] <= d[(j + 1) as int]);
            }
        }
        
        j = j + 1;
    }
    
    (i, j)
}
// </vc-code>

fn main() {
}

}