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
spec fn sorted(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < q.len() ==> q[i] <= q[j]
}

spec fn inv(a: Seq<int>, a1: Seq<int>, a2: Seq<int>, i: nat, mid: nat) -> bool {
    (i <= a1.len()) && (i <= a2.len()) && (i + mid <= a.len()) &&
    (a1.subrange(0, i as int) =~= a.subrange(0, i as int)) && 
    (a2.subrange(0, i as int) =~= a.subrange(mid as int, (i + mid) as int))
}

fn merge(b: &mut Vec<int>, c: &Vec<int>, d: &Vec<int>)
    requires
        old(b).len() == c.len() + d.len(),
        sorted(c@),
        sorted(d@),
    ensures
        sorted(b@),
        b@.to_multiset() == c@.to_multiset().add(d@.to_multiset()),
{
    let mut i: usize = 0;
    let mut j: usize = 0;
    let mut k: usize = 0;

    while i < c@.len() && j < d@.len()
        invariant
            i <= c@.len(),
            j <= d@.len(),
            k == i + j,
            k <= b@.len(),
            inv_sorted(b@, c@, d@, i as nat, j as nat),
            inv_sub_set(b@, c@, d@, i as nat, j as nat),
    {
        proof { let old_b = b@; }
        proof { let old_i = i as nat; }
        proof { let old_j = j as nat; }
        proof { assert(sorted(old_b.subrange(0, k as int))); }
        proof { if k > 0 { assert(old_b@[k-1] <= c@[i] && old_b@[k-1] <= d@[j]); } }
        if c@[i] <= d@[j] {
            b[k] = c@[i];
            proof { lemma_add_from_c(old_b, c@, d@, old_i, old_j, b@); }
            proof { assert(sorted(b@.subrange(0, (k + 1) as int))); }
            i += 1;
            k += 1;
        } else {
            b[k] = d@[j];
            proof { lemma_add_from_d(old_b, c@, d@, old_i, old_j, b@); }
            proof { assert(sorted(b@.subrange(0, (k + 1) as int))); }
            j += 1;
            k += 1;
        }
    }

    while i < c@.len()
        invariant
            i <= c@.len(),
            j == d@.len(),
            k == i + j,
            k <= b@.len(),
            inv_sorted(b@, c@, d@, i as nat, j as nat),
            inv_sub_set(b@, c@, d@, i as nat, j as nat),
    {
        proof { let old_b = b@; }
        proof { let old_i = i as nat; }
        proof { let old_j = j as nat; }
        proof { assert(sorted(old_b.subrange(0, k as int))); }
        proof { if k > 0 { assert(old_b@[k-1] <= c@[i]); } }
        b[k] = c@[i];
        proof { lemma_add_from_c(old_b, c@, d@, old_i, old_j, b@); }
        proof { assert(sorted(b@.subrange(0, (k + 1) as int))); }
        i += 1;
        k += 1;
    }

    while j < d@.len()
        invariant
            i == c@.len(),
            j <= d@.len(),
            k == i + j,
            k <= b@.len(),
            inv_sorted(b@, c@, d@, i as nat, j as nat),
            inv_sub_set(b@, c@, d@, i as nat, j as nat),
    {
        proof { let old_b = b@; }
        proof { let old_i = i as nat; }
        proof { let old_j = j as nat; }
        proof { assert(sorted(old_b.subrange(0, k as int))); }
        proof { if k > 0 { assert(old_b@[k-1] <= d@[j]); } }
        b[k] = d@[j];
        proof { lemma_add_from_d(old_b, c@, d@, old_i, old_j, b@); }
        proof { assert(sorted(b@.subrange(0, (k + 1) as int))); }
        j += 1;
        k += 1;
    }
}

spec fn inv_sorted(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat) -> bool {
    i <= c.len() && j <= d.len() && i + j <= b.len() &&
    ((i + j > 0 && i < c.len()) ==> (b[(j + i - 1) as int] <= c[i as int])) &&
    ((i + j > 0 && j < d.len()) ==> (b[(j + i - 1) as int] <= d[j as int])) &&
    sorted(b.subrange(0, (i + j) as int))
}

spec fn inv_sub_set(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat) -> bool {
    i <= c.len() && j <= d.len() && i + j <= b.len() &&
    b.subrange(0, (i + j) as int).to_multiset() == 
        c.subrange(0, i as int).to_multiset().add(d.subrange(0, j as int).to_multiset())
}

proof fn lemma_multiset_full(b: Seq<int>, c: Seq<int>, d: Seq<int>)
    requires
        b.to_multiset() == c.subrange(0, c.len() as int).to_multiset().add(d.subrange(0, d.len() as int).to_multiset()),
    ensures
        b.to_multiset() == c.to_multiset().add(d.to_multiset()),
{
    assert(b.to_multiset() == c.to_multiset().add(d.to_multiset()));
}

proof fn lemma_add_from_c(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat, b_new: Seq<int>)
    requires
        i < c.len(),
        j <= d.len(),
        inv_sub_set(b, c, d, i, j),
        b_new == b.update((i + j) as int, c[i as int]),
        i + j < b_new.len(),
    ensures
        inv_sub_set(b_new, c, d, (i + 1) as nat, j as nat),
{
    let new_i = i + 1;
    let prefix_len = (new_i + j) as int;
    assert(b_new.subrange(0, prefix_len).to_multiset() == 
        c.subrange(0, new_i as int).to_multiset().add(d.subrange(0, j as int).to_multiset()));
}

proof fn lemma_add_from_d(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat, b_new: Seq<int>)
    requires
        j < d.len(),
        i <= c.len(),
        inv_sub_set(b, c, d, i, j),
        b_new == b.update((i + j) as int, d[j as int]),
        i + j < b_new.len(),
    ensures
        inv_sub_set(b_new, c, d, i as nat, (j + 1) as nat),
{
    let new_j = j + 1;
    let prefix_len = (i + new_j) as int;
    assert(b_new.subrange(0, prefix_len).to_multiset() == 
        c.subrange(0, i as int).to_multiset().add(d.subrange(0, new_j as int).to_multiset()));
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
    proof {
        let mid_int = mid as int;
        let left_seq = a@.subrange(0, mid_int);
        let right_seq = a@.subrange(mid_int, a@.len() as int);
    }
    let left_seq = a@.subrange(0, mid as int);
    let right_seq = a@.subrange(mid as int, a@.len() as int);
    let left_vec = left_seq.to_vec();
    let right_vec = right_seq.to_vec();
    let sorted_left = merge_sort(left_vec);
    let sorted_right = merge_sort(right_vec);
    let mut result = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.len() == i,
            i <= a.len(),
    {
        result.push(0);
        i += 1;
    }
    assert(result.len() == a.len());
    merge(&mut result, &sorted_left, &sorted_right);
    result
}
// </vc-code>

fn main() {}

}