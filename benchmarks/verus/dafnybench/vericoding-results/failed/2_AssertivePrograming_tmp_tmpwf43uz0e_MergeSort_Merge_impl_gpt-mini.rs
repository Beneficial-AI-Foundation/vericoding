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
spec fn merge_seq(c: Seq<i32>, d: Seq<i32>) -> Seq<i32> {
    if c.len() == 0 {
        d
    } else if d.len() == 0 {
        c
    } else {
        // use int indices for sequence access
        if c[0] <= d[0] {
            seq![c[0]] + merge_seq(c.subrange(1, c.len()), d)
        } else {
            seq![d[0]] + merge_seq(c, d.subrange(1, d.len()))
        }
    }
}

proof fn lemma_merge_seq_len(c: Seq<i32>, d: Seq<i32>) 
    ensures merge_seq(c, d).len() == c.len() + d.len()
{
    decreases (c.len(), d.len());
    if c.len() == 0 {
        // merge_seq(c,d) == d
    } else if d.len() == 0 {
        // merge_seq(c,d) == c
    } else {
        if c[0] <= d[0] {
            lemma_merge_seq_len(c.subrange(1, c.len()), d);
        } else {
            lemma_merge_seq_len(c, d.subrange(1, d.len()));
        }
    }
}

proof fn lemma_merge_seq_sorted(c: Seq<i32>, d: Seq<i32>) 
    requires sorted(c) && sorted(d)
    ensures sorted(merge_seq(c, d))
{
    decreases (c.len(), d.len());
    if c.len() == 0 || d.len() == 0 {
        // merge_seq is one of them, sorted by requirement
    } else {
        if c[0] <= d[0] {
            // merge_seq = [c[0]] + merge_seq(c[1..], d)
            lemma_merge_seq_sorted(c.subrange(1, c.len()), d);
            // The recursive call and the ordering c[0] <= d[0] and sorted(c) suffice.
        } else {
            // symmetric case
            lemma_merge_seq_sorted(c, d.subrange(1, d.len()));
        }
    }
}

proof fn lemma_merge_seq_multiset(c: Seq<i32>, d: Seq<i32>)
    ensures merge_seq(c, d).to_multiset() == c.to_multiset().add(d.to_multiset())
{
    decreases (c.len(), d.len());
    if c.len() == 0 {
        // merge_seq == d
    } else if d.len() == 0 {
        // merge_seq == c
    } else {
        if c[0] <= d[0] {
            lemma_merge_seq_multiset(c.subrange(1, c.len()), d);
            // merge_seq = [c[0]] + merge_seq(c[1..], d)
            // hence multiset adds c[0]
        } else {
            lemma_merge_seq_multiset(c, d.subrange(1, d.len()));
            // similar
        }
    }
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
    // Compute the merged sequence as a pure/spec value
    let res = merge_seq(c@, d@);

    // Prove length property
    proof {
        lemma_merge_seq_len(c@, d@);
    }
    assert(res.len() == c@.len() + d@.len());
    assert(res.len() == b.len()); // precondition ensures b.len() == c.len()+d.len()

    // Copy elements from the spec sequence into the mutable vector b
    let mut k: usize = 0;
    while k < b.len() 
        invariant k <= b.len();
        invariant (forall |t: int| 0 <= t && t < (k as int) ==> b@[t] == res@[t]);
        decreases b.len() - k;
    {
        b.set(k, res@[k]);
        k = k + 1;
    }

    // After copying, b@ equals res
    assert(forall |i: int| 0 <= i && i < b@.len() ==> b@[i] == res@[i]);
    assert(b@ == res);

    // Now use lemmas to conclude the ensures
    proof {
        lemma_merge_seq_sorted(c@, d@);
        lemma_merge_seq_multiset(c@, d@);
    }
    assert(sorted(b@)); 
    assert(b@.to_multiset() == c@.to_multiset().add(d@.to_multiset()));
}
// </vc-code>

fn main() {}

}