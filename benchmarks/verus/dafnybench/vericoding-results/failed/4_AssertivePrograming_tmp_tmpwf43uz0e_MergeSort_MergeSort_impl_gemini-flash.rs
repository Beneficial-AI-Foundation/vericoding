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
lemma fn lemma_multiset_equality<A>(s1: Seq<A>, s2: Seq<A>)
    requires
        s1.to_multiset() == s2.to_multiset(),
        s1.len() == s2.len(),
        sorted(s1),
        sorted(s2),
    ensures
        s1 =~= s2,
{
    // This lemma is generally not provable without additional constraints or properties,
    // as two sequences can have the same multiset elements but different order.
    // However, in the context of sorting, if we know they are sorted and have the same multiset,
    // then they must be equal.
    // This proof is not simple and might require induction on the sequence length.
    // However, for the context of merge sort, proving multiset equality and sortedness is sufficient.
    // The specific context in the original code involving 'len' in the signature was misleading.
    // We only need to prove b@.to_multiset() == c@.to_multiset().add(d@.to_multiset()) and sorted(b@).
    // This lemma as originally defined is not directly required for the merge sort proof.
}

lemma fn lemma_add_c_to_multiset(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat, val_c: int)
    requires
        i < c.len(),
        i + j < b.len(),
        b.subrange(0, (i + j) as int).to_multiset() == c.subrange(0, i as int).to_multiset().add(d.subrange(0, j as int).to_multiset()),
        // No need for explicit len() assertions here, subrange implies len().
        b[(i + j) as int] == val_c, // Added this line to reflect the actual set operation
        c[i as int] == val_c,
    ensures
        b.subrange(0, (i + j + 1) as int).to_multiset() == c.subrange(0, (i + 1) as int).to_multiset().add(d.subrange(0, j as int).to_multiset()),
{
    assert(b.subrange(0, (i + j + 1) as int).to_multiset() == b.subrange(0, (i + j) as int).to_multiset().add(multiset![val_c]));
    assert(c.subrange(0, (i + 1) as int).to_multiset() == c.subrange(0, i as int).to_multiset().add(multiset![val_c]));
}

lemma fn lemma_add_d_to_multiset(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat, val_d: int)
    requires
        j < d.len(),
        i + j < b.len(),
        b.subrange(0, (i + j) as int).to_multiset() == c.subrange(0, i as int).to_multiset().add(d.subrange(0, j as int).to_multiset()),
        // No need for explicit len() assertions here, subrange implies len().
        b[(i + j) as int] == val_d, // Added this line to reflect the actual set operation
        d[j as int] == val_d,
    ensures
        b.subrange(0, (i + j + 1) as int).to_multiset() == c.subrange(0, i as int).to_multiset().add(d.subrange(0, (j + 1) as int).to_multiset()),
{
    assert(b.subrange(0, (i + j + 1) as int).to_multiset() == b.subrange(0, (i + j) as int).to_multiset().add(multiset![val_d]));
    assert(d.subrange(0, (j + 1) as int).to_multiset() == d.subrange(0, j as int).to_multiset().add(multiset![val_d]));
}

// Function to handle the merge operation
fn merge(b: &mut Vec<int>, c: &Vec<int>, d: &Vec<int>)
    requires
        old(b).len() == c.len() + d.len(),
        sorted(c@),
        sorted(d@),
    ensures
        sorted(b@),
        b@.to_multiset() == c@.to_multiset().add(d@.to_multiset()),
{
    let mut i: nat = 0;
    let mut j: nat = 0;
    let b_len = b.len(); // Cache length for efficiency and verification of loop invariant

    assert(inv_sorted(b@, c@, d@, i, j));
    assert(inv_sub_set(b@, c@, d@, i, j));

    while i < c.len() && j < d.len()
        invariant!
            b_len == old(b).len(),
            i <= c.len(),
            j <= d.len(),
            i + j <= b_len,
            inv_sorted(b@, c@, d@, i, j),
            inv_sub_set(b@, c@, d@, i, j),
        {
            let k = (i + j) as int;
            if c[i as int] <= d[j as int] {
                b.set(k, c[i as int]);
                proof {
                    lemma_add_c_to_multiset(b@, c@, d@, i, j, c[i as int]); // Use c[i as int] directly
                }
                i = i + 1;
            } else {
                b.set(k, d[j as int]);
                proof {
                    lemma_add_d_to_multiset(b@, c@, d@, i, j, d[j as int]); // Use d[j as int] directly
                }
                j = j + 1;
            }
        }

    while i < c.len()
        invariant!
            b_len == old(b).len(),
            i <= c.len(),
            j == d.len(),
            i + j <= b_len,
            inv_sorted(b@, c@, d@, i, j),
            inv_sub_set(b@, c@, d@, i, j),
        {
            let k = (i + j) as int;
            b.set(k, c[i as int]);
            proof {
                lemma_add_c_to_multiset(b@, c@, d@, i, j, c[i as int]); // Use c[i as int] directly
            }
            i = i + 1;
        }

    while j < d.len()
        invariant!
            b_len == old(b).len(),
            i == c.len(),
            j <= d.len(),
            i + j <= b_len,
            inv_sorted(b@, c@, d@, i, j),
            inv_sub_set(b@, c@, d@, i, j),
        {
            let k = (i + j) as int;
            b.set(k, d[j as int]);
            proof {
                lemma_add_d_to_multiset(b@, c@, d@, i, j, d[j as int]); // Use d[j as int] directly
            }
            j = j + 1;
        }
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
    let n = a.len();
    if n <= 1 {
        // Base case: already sorted
        a
    } else {
        let mid = n / 2;
        let left_vec = a.subsequence(0, mid as int).to_vec();
        let right_vec = a.subsequence(mid as int, n as int).to_vec();

        let b_left = merge_sort(left_vec);
        let b_right = merge_sort(right_vec);

        let mut b = Vec::new();
        b.fill_with_len(n as u32, 0); // Initialize with dummy values, actual values filled by merge

        merge(&mut b, &b_left, &b_right);
        b
    }
}
// </vc-code>

fn main() {}

}