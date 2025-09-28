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
pub proof fn merge_update_multiset_preserves(b: Seq<int>, c: Seq<int>, d: Seq<int>, old_i: nat, old_j: nat, chosen: int, from_c: bool)
    requires
        inv_sub_set(b, c, d, old_i, old_j),
    ensures
        ({
            let new_i = if from_c { old_i + 1 } else { old_i };
            let new_j = if from_c { old_j } else { old_j + 1 };
            let k = old_i as int + old_j as int;
            let new_b = b.update(k, chosen);
            inv_sub_set(new_b, c, d, new_i, new_j)
        })
    {
        let k = old_i as int + old_j as int;
        let new_i = if from_c { old_i + 1 } else { old_i };
        let new_j = if from_c { old_j } else { old_j + 1 };
        let new_b = b.update(k, chosen);
        let new_k = k + 1;

        if new_k as nat <= b.len() {
            assert(new_b.subrange(0, new_k).to_multiset() =~= b.subrange(0, k).to_multiset().add(Multiset::singleton(chosen)));
        }

        if from_c {
            assert(chosen == *c.index(old_i as usize));
            assert(c.subrange(0, new_i as int).to_multiset() =~= c.subrange(0, old_i as int).to_multiset().add(Multiset::singleton(chosen)));
            assert(d.subrange(0, new_j as int).to_multiset() =~= d.subrange(0, old_j as int).to_multiset());
        } else {
            assert(chosen == *d.index(old_j as usize));
            assert(d.subrange(0, new_j as int).to_multiset() =~= d.subrange(0, old_j as int).to_multiset().add(Multiset::singleton(chosen)));
            assert(c.subrange(0, new_i as int).to_multiset() =~= c.subrange(0, old_i as int).to_multiset());
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
    let k = i0 + j0;
    let mut new_i: usize = i0;
    let mut new_j: usize = j0;
    let mut chosen: int = 0; // dummy

    if i0 < c.len() {
        if j0 < d.len() {
            if c[i0] <= d[j0] {
                chosen = c[i0];
                new_i = i0 + 1;
            } else {
                chosen = d[j0];
                new_j = j0 + 1;
            }
        } else {
            chosen = c[i0];
            new_i = i0 + 1;
        }
    } else {
        chosen = d[j0];
        new_j = j0 + 1;
    }
    b.set(k, chosen);
    proof {
        // Call the lemma to establish the multiset invariant holds for the updated b
        merge_update_multiset_preserves(old(b)@, c@, d@, i0 as nat, j0 as nat, chosen, if new_i > i0 { true } else { false });
        // Assert the sorted invariant for the updated prefix
        assert(sorted(b@.subrange(0, (new_i as int + new_j as int))));
        // Assert the next elements are greater or equal to the last added element
        if new_i < c.len() && new_i + new_j > 0 {
            assert(chosen <= *c@.index(new_i));
        }
        if new_j < d.len() && new_i + new_j > 0 {
            assert(chosen <= *d@.index(new_j));
        }
    }
    (new_i, new_j)
}
// </vc-code>

fn main() {
}

}