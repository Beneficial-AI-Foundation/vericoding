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
proof lemma_merge_sorted_eq_next(b: Seq<i32>, c: Seq<i32>, d: Seq<i32>, i: usize, j: usize)
    requires
        inv_sorted(b, c, d, i, j),
        j < d.len(),
        i < c.len(),
        i + j > 0,
    ensures
        d[j] >= b[i + j - 1],
        c[i] >= b[i + j - 1],
{
    assert(i + j > 0);
    assert(b[i + j - 1] <= d[j]);
    assert(b[i + j - 1] <= c[i]);
}

proof lemma_inv_sorted_preserved(b: Seq<i32>, c: Seq<i32>, d: Seq<i32>, i: usize, j: usize, i1: usize, j1: usize)
    requires
        inv_sorted(b, c, d, i, j),
        i <= i1 <= c.len(),
        j <= j1 <= d.len(),
        i1 + j1 <= b.len(),
        (i1 == i + 1 && j1 == j) ==> (i < c.len() && (j == d.len() || c[i] <= d[j])),
        (i1 == i && j1 == j + 1) ==> (j < d.len() && (i == c.len() || d[j] <= c[i])),
    ensures
        inv_sorted(b, c, d, i1, j1),
{
    if i1 == i + 1 && j1 == j {
        assert(i < c.len());
        assert(j == d.len() || c[i] <= d[j]);
        
        let new_len = i1 + j1;
        let last_index = new_len - 1;
        
        assert(sorted(b.subrange(0, new_len as int)));
        
        if new_len > 0 {
            if i1 < c.len() {
                assert(b[last_index] == c[i]);
                assert(c[i] <= c[i1]);
            }
            if j1 < d.len() {
                assert(b[last_index] == c[i]);
                assert(j == d.len() || c[i] <= d[j]);
            }
        }
    } else if i1 == i && j1 == j + 1 {
        assert(j < d.len());
        assert(i == c.len() || d[j] <= c[i]);
        
        let new_len = i1 + j1;
        let last_index = new_len - 1;
        
        assert(sorted(b.subrange(0, new_len as int)));
        
        if new_len > 0 {
            if i1 < c.len() {
                assert(b[last_index] == d[j]);
                assert(i == c.len() || d[j] <= c[i]);
            }
            if j1 < d.len() {
                assert(b[last_index] == d[j]);
                assert(d[j] <= d[j1]);
            }
        }
    }
}

proof lemma_inv_sub_set_preserved(b: Seq<i32>, c: Seq<i32>, d: Seq<i32>, i: usize, j: usize, i1: usize, j1: usize)
    requires
        inv_sub_set(b, c, d, i, j),
        i <= i1 <= c.len(),
        j <= j1 <= d.len(),
        i1 + j1 <= b.len(),
        (i1 == i + 1 && j1 == j) ==> (i < c.len()),
        (i1 == i && j1 == j + 1) ==> (j < d.len()),
    ensures
        inv_sub_set(b, c, d, i1, j1),
{
    if i1 == i + 1 && j1 == j {
        assert(i < c.len());
        let old_prefix = b.subrange(0, (i + j) as int).to_multiset();
        let new_prefix = b.subrange(0, (i1 + j1) as int).to_multiset();
        let c_prefix = c.subrange(0, i as int).to_multiset();
        let d_prefix = d.subrange(0, j as int).to_multiset();
        let new_c_prefix = c.subrange(0, i1 as int).to_multiset();
        
        assert(new_prefix == old_prefix.add(b@[(i + j) as int].to_multiset()));
        assert(new_c_prefix == c_prefix.add(c@[i as int].to_multiset()));
        assert(b@[(i + j) as int] == c[i]);
    } else if i1 == i && j1 == j + 1 {
        assert(j < d.len());
        let old_prefix = b.subrange(0, (i + j) as int).to_multiset();
        let new_prefix = b.subrange(0, (i1 + j1) as int).to_multiset();
        let c_prefix = c.subrange(0, i as int).to_multiset();
        let d_prefix = d.subrange(0, j as int).to_multiset();
        let new_d_prefix = d.subrange(0, j1 as int).to_multiset();
        
        assert(new_prefix == old_prefix.add(b@[(i + j) as int].to_multiset()));
        assert(new_d_prefix == d_prefix.add(d@[j as int].to_multiset()));
        assert(b@[(i + j) as int] == d[j]);
    }
}

proof lemma_final_invariant_implies_post(b: Seq<i32>, c: Seq<i32>, d: Seq<i32>)
    requires
        inv_sub_set(b, c, d, c.len(), d.len()),
        inv_sorted(b, c, d, c.len(), d.len()),
        b.len() == c.len() + d.len(),
    ensures
        sorted(b),
        b.to_multiset() == c.to_multiset().add(d.to_multiset()),
{
    assert(b.subrange(0, b.len() as int) == b);
    assert(c.subrange(0, c.len() as int) == c);
    assert(d.subrange(0, d.len() as int) == d);
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
    
    assert(i == 0 && j == 0);
    assert(inv_sub_set(b@, c@, d@, i, j));
    assert(inv_sorted(b@, c@, d@, i, j));
    
    while i < c.len() || j < d.len()
        invariant
            i <= c.len(),
            j <= d.len(),
            i + j <= b@.len(),
            inv_sub_set(b@, c@, d@, i, j),
            inv_sorted(b@, c@, d@, i, j),
        decreases
            c.len() - i + d.len() - j,
    {
        if i == c.len() {
            proof {
                lemma_inv_sub_set_preserved(b@, c@, d@, i, j, i, j+1);
                lemma_inv_sorted_preserved(b@, c@, d@, i, j, i, j+1);
            }
            b.set(i + j, d[j]);
            j = j + 1;
        } else if j == d.len() {
            proof {
                lemma_inv_sub_set_preserved(b@, c@, d@, i, j, i+1, j);
                lemma_inv_sorted_preserved(b@, c@, d@, i, j, i+1, j);
            }
            b.set(i + j, c[i]);
            i = i + 1;
        } else {
            if d[j] < c[i] {
                proof {
                    lemma_inv_sub_set_preserved(b@, c@, d@, i, j, i, j+1);
                    lemma_merge_sorted_eq_next(b@, c@, d@, i, j);
                    lemma_inv_sorted_preserved(b@, c@, d@, i, j, i, j+1);
                }
                b.set(i + j, d[j]);
                j = j + 1;
            } else {
                proof {
                    lemma_inv_sub_set_preserved(b@, c@, d@, i, j, i+1, j);
                    lemma_merge_sorted_eq_next(b@, c@, d@, i, j);
                    lemma_inv_sorted_preserved(b@, c@, d@, i, j, i+1, j);
                }
                b.set(i + j, c[i]);
                i = i + 1;
            }
        }
    }
    
    proof {
        lemma_final_invariant_implies_post(b@, c@, d@);
    }
}
// </vc-code>

fn main() {}

}