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
lemma fn lemma_update_sorted_i(old_b: Seq<int>, new_b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat)
    requires
        i < c.len(),
        inv_sorted(old_b, c, d, i as nat, j as nat),
        new_b.len() == (i + j + 1) as int, // b represents the new, extended sequence
        new_b.subrange(0, (i+j) as int) =~= old_b.subrange(0, (i+j) as int), // The prefix is unchanged
        new_b[(j + i) as int] == c[i as int],
        sorted(c),
        sorted(d),
        (j == d.len() || new_b[(j+i) as int] <= d[j as int])
    ensures
        inv_sorted(new_b, c, d, (i + 1) as nat, j as nat)
{
    // Prove sorted(new_b.subrange(0, (i+j+1) as int))
    assert(sorted(old_b.subrange(0, (i+j) as int))) by {
        // This is part of the inv_sorted(old_b, c, d, i, j)
    };
    assert(new_b.subrange(0, (i+j) as int) =~= old_b.subrange(0, (i+j) as int));
    assert(sorted(new_b.subrange(0, (i+j) as int)));

    if (i+j) > 0 {
        // We need to show new_b[(i+j-1) as int] <= new_b[(i+j) as int]
        // new_b[(i+j) as int] is c[i]
        // new_b[(i+j-1) as int] is old_b[(i+j-1) as int]
        // From inv_sorted(old_b, c, d, i, j), we have:
        // ((i + j - 1 > 0 && i < c.len()) ==> (old_b[(j + i - 1) as int] <= c[i as int]))
        // This implication refers to the relationship of the last element of the sorted prefix with the next element in c
        // or d, based on which one might be picked next.
        // What we need to show for sortedness is that the last element BEFORE c[i] (which is new_b[i+j-1])
        // is less than or equal to c[i].
        // Since old_b.subrange(0, i+j) was sorted, old_b[i+j-1] <= old_b[k] for k < i+j-1 isn't what we need.
        // We need that the largest element in new_b.subrange(0, i+j) is <= new_b[i+j].
        if i > 0 && old_b[(i+j-1) as int] == c[(i-1) as int] {
            assert(c[(i-1) as int] <= c[i as int]); // Because c is sorted
            assert(new_b[(i+j-1) as int] <= new_b[(i+j) as int]);
        } else if j > 0 && old_b[(i+j-1) as int] == d[(j-1) as int] {
            // Need to show d[j-1] <= c[i]
            // This comes from the logic of merge sort that if d[j-1] was chosen over c[i-1] (if i-1 exists),
            // and now c[i] is chosen, it must be the case that c[i] >= d[j-1].
            // Or, more generally, because inv_sorted(old_b, c, d, i, j) holds, we know for old_b:
            // ((i + j - 1 > 0 && i < c.len()) ==> (old_b[(j + i - 1) as int] <= c[i as int]))
            // This is the key: old_b[(i+j-1) as int] must be <= c[i as int] if c[i] is taken next
            // (or if d[j] is taken next, then old_b[(i+j-1)] <= d[j]).
            // Since c[i] is being taken now, and old_b[(i+j-1) as int] is the largest element in the old sorted prefix,
            // (by definition of sortedness), it must be <= c[i].
            // If old_b[(j + i - 1) as int] was from d, and c[i] is picked now, it implies that either i==c.len() (not this case)
            // or c[i] <= d[j].
            // No, the inv_sorted has this part: `((i + j > 0 && j < d.len()) ==> (b[(j + i - 1) as int] <= d[j as int]))`
            // And this part: `(i + j > 0 && i < c.len()) ==> (b[(j + i - 1) as int] <= c[i as int])`
            // If the element at index (i+j-1) was old_b[(i+j-1)], then
            // IF i < c.len(): old_b[(i+j-1)] <= c[i].
            //   In our case, new_b[(i+j-1)] = old_b[(i+j-1)], new_b[(i+j)] = c[i].
            //   So if i < c.len(), then old_b[(i+j-1)] <= c[i] implies new_b[(i+j-1)] <= new_b[(i+j)].
            assert(new_b[(i+j-1) as int] <= new_b[(i+j) as int]); // If old_b[(i+j-1)] came from c, then we need to prove c[(i-1)] <= c[i]
        } else {
            // This handles the case where i+j is 0, i.e., first element.
            // In this case (i+j) will be 0 and `if (i+j) > 0` condition fails. No assertion needed.
        }
    }
    
    // Now verify the post-conditions for inv_sorted(new_b, c, d, (i+1), j)
    // inv_sorted post-condition 1: (i+j+1 > 0 && i+1 < c.len()) ==> (new_b[(j + i) as int] <= c[(i + 1) as int])
    if (i + j + 1 > 0 && (i + 1) < c.len()) {
        assert(c[i as int] <= c[(i + 1) as int]) by {
            assert(sorted(c));
        }; // Since c is sorted
        assert(new_b[(j + i) as int] == c[i as int]);
        assert(new_b[(j + i) as int] <= c[(i + 1) as int]);
    }
    // inv_sorted post-condition 2: (i+j+1 > 0 && j < d.len()) ==> (new_b[(j + i) as int] <= d[j as int])
    if (i + j + 1 > 0 && j < d.len()) {
        assert(new_b[(j + i) as int] <= d[j as int]); // This is guaranteed by the 'requires' clause (j == d.len() || b[(j+i) as int] <= d[j as int])
    }
    assert(sorted(new_b.subrange(0, (i+j+1) as int)));
}

lemma fn lemma_update_sorted_j(old_b: Seq<int>, new_b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat)
    requires
        j < d.len(),
        inv_sorted(old_b, c, d, i as nat, j as nat),
        new_b.len() == (i + j + 1) as int, // b represents the new, extended sequence
        new_b.subrange(0, (i+j) as int) =~= old_b.subrange(0, (i+j) as int),
        new_b[(j + i) as int] == d[j as int],
        sorted(c),
        sorted(d),
        (i == c.len() || new_b[(j+i) as int] <= c[i as int])
    ensures
        inv_sorted(new_b, c, d, i as nat, (j + 1) as nat)
{
    assert(sorted(old_b.subrange(0, (i+j) as int)));
    assert(new_b.subrange(0, (i+j) as int) =~= old_b.subrange(0, (i+j) as int));
    assert(sorted(new_b.subrange(0, (i+j) as int)));

    if (i+j) > 0 {
        // We need to show new_b[(i+j-1) as int] <= new_b[(i+j) as int]
        // new_b[(i+j) as int] is d[j]
        // new_b[(i+j-1) as int] is old_b[(i+j-1) as int]
        if j > 0 && old_b[(i+j-1) as int] == d[(j-1) as int] {
            assert(d[(j-1) as int] <= d[j as int]); // Because d is sorted
            assert(new_b[(i+j-1) as int] <= new_b[(i+j) as int]);
        } else if i > 0 && old_b[(i+j-1) as int] == c[(i-1) as int] {
            // Need to show c[i-1] <= d[j]
            // From inv_sorted(old_b, c, d, i, j), if present, element old_b[(i+j-1)] <= d[j] if d[j] is the next element taken.
            // If i < c.len(): old_b[(i+j-1)] <= d[j].
            //   In our case, new_b[(i+j-1)] = old_b[(i+j-1)], new_b[(i+j)] = d[j].
            //   So if i < c.len(), then old_b[(i+j-1)] <= d[j] implies new_b[(i+j-1)] <= new_b[(i+j)].
            assert(new_b[(i+j-1) as int] <= new_b[(i+j) as int]); // If old_b[(i+j-1)] came from d, then we need to prove d[(j-1)] <= d[j]
        } else {
            // First element case
        }
    }

    // Now verify the post-conditions for inv_sorted(new_b, c, d, i, (j+1))
    // inv_sorted post-condition 1: (i+j+1 > 0 && i < c.len()) ==> (new_b[(j + i) as int] <= c[i as int])
    if (i + j + 1 > 0 && i < c.len()) {
         assert(new_b[(j + i) as int] <= c[i as int]); // This is guaranteed by the 'requires' clause (i == c.len() || b[(j+i) as int] <= c[i as int])
    }
    // inv_sorted post-condition 2: (i+j+1 > 0 && j+1 < d.len()) ==> (new_b[(j + i) as int] <= d[(j + 1) as int])
    if (i + j + 1 > 0 && (j + 1) < d.len()) {
        assert(d[j as int] <= d[(j + 1) as int]) by {
            assert(sorted(d));
        }; // Since d is sorted
        assert(new_b[(j + i) as int] == d[j as int]);
        assert(new_b[(j + i) as int] <= d[(j + 1) as int]);
    }
    assert(sorted(new_b.subrange(0, (i+j+1) as int)));
}

lemma fn lemma_update_sub_set_i(b_old: Seq<int>, b_new: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat)
    requires
        i < c.len(),
        inv_sub_set(b_old, c, d, i as nat, j as nat),
        b_new.len() == (i + j + 1) as int,
        b_new.subrange(0, (i+j) as int) =~= b_old.subrange(0, (i+j) as int),
        b_new[(j + i) as int] == c[i as int]
    ensures
        inv_sub_set(b_new, c, d, (i + 1) as nat, j as nat)
{
    assert(b_new.subrange(0, (i + j + 1) as int).to_multiset() =~=
           b_old.subrange(0, (i + j) as int).to_multiset().add(multiset![c[i as int]]));
    assert(b_old.subrange(0, (i+j) as int).to_multiset() =~=
           c.subrange(0, i as int).to_multiset().add(d.subrange(0, j as int).to_multiset()));
    assert(c.subrange(0, (i+1) as int).to_multiset() =~=
           c.subrange(0, i as int).to_multiset().add(multiset![c[i as int]]));
    assert(b_new.subrange(0, (i + j + 1) as int).to_multiset() =~=
           c.subrange(0, (i + 1) as int).to_multiset().add(d.subrange(0, j as int).to_multiset()));
}

lemma fn lemma_update_sub_set_j(b_old: Seq<int>, b_new: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat)
    requires
        j < d.len(),
        inv_sub_set(b_old, c, d, i as nat, j as nat),
        b_new.len() == (i + j + 1) as int,
        b_new.subrange(0, (i+j) as int) =~= b_old.subrange(0, (i+j) as int),
        b_new[(j + i) as int] == d[j as int]
    ensures
        inv_sub_set(b_new, c, d, i as nat, (j + 1) as nat)
{
    assert(b_new.subrange(0, (i + j + 1) as int).to_multiset() =~=
           b_old.subrange(0, (i + j) as int).to_multiset().add(multiset![d[j as int]]));
    assert(b_old.subrange(0, (i+j) as int).to_multiset() =~=
           c.subrange(0, i as int).to_multiset().add(d.subrange(0, j as int).to_multiset()));
    assert(d.subrange(0, (j+1) as int).to_multiset() =~=
           d.subrange(0, j as int).to_multiset().add(multiset![d[j as int]]));
    assert(b_new.subrange(0, (i + j + 1) as int).to_multiset() =~=
           c.subrange(0, i as int).to_multiset().add(d.subrange(0, (j + 1) as int).to_multiset()));
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
    let k = i + j;

    let old_b_seq = b.seq; // Capture the ghost sequence before any changes

    if i < c.len() && (j == d.len() || c.int_index(i as int) <= d.int_index(j as int)) {
        b.set(k as usize, c.int_index(i as int));
        proof {
            let pre_b_seq = old_b_seq;
            let post_b_seq = old_b_seq.update(k as int, c.int_index(i as int));

            lemma_update_sorted_i(pre_b_seq, post_b_seq, c.seq, d.seq, i as nat, j as nat);
            lemma_update_sub_set_i(pre_b_seq, post_b_seq, c.seq, d.seq, i as nat, j as nat);
        }
        i = i + 1;
    } else {
        b.set(k as usize, d.int_index(j as int));
        proof {
            let pre_b_seq = old_b_seq;
            let post_b_seq = old_b_seq.update(k as int, d.int_index(j as int));

            lemma_update_sorted_j(pre_b_seq, post_b_seq, c.seq, d.seq, i as nat, j as nat);
            lemma_update_sub_set_j(pre_b_seq, post_b_seq, c.seq, d.seq, i as nat, j as nat);
        }
        j = j + 1;
    }
    (i, j)
}
// </vc-code>

fn main() {
}

}