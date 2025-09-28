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
lemma fn muliset_eq(b: Seq<i32>, c: Seq<i32>, d: Seq<i32>)
    requires
        b.len() == c.len() + d.len(),
        b.subrange(0, b.len() as int).to_multiset() == c.subrange(0, c.len() as int).to_multiset().add(d.subrange(0, d.len() as int).to_multiset()),
    ensures
        b.to_multiset() == c.to_multiset().add(d.to_multiset()),
{
    assert(b.to_multiset() == b.subrange(0, b.len() as int).to_multiset());
    assert(c.to_multiset() == c.subrange(0, c.len() as int).to_multiset());
    assert(d.to_multiset() == d.subrange(0, d.len() as int).to_multiset());
}

lemma fn lemma_add_c_multiset(b: Seq<i32>, c: Seq<i32>, d: Seq<i32>, i: usize, j: usize, val_c: i32)
    requires
        i < c.len(),
        b.subrange(0, (i + j) as int).to_multiset() == c.subrange(0, i as int).to_multiset().add(d.subrange(0, j as int).to_multiset()),
        b.len() >= (i + j + 1) as int,
        b[(i+j) as int] == val_c,
        c[i as int] == val_c,
    ensures
        b.subrange(0, (i + j + 1) as int).to_multiset() == c.subrange(0, (i + 1) as int).to_multiset().add(d.subrange(0, j as int).to_multiset()),
{
    assert(b.subrange(0, (i + j + 1) as int).to_multiset() == b.subrange(0, (i + j) as int).to_multiset().add(multiset![b[(i+j) as int]]));
    assert(c.subrange(0, (i + 1) as int).to_multiset() == c.subrange(0, i as int).to_multiset().add(multiset![c[i as int]]));
}

lemma fn lemma_add_d_multiset(b: Seq<i32>, c: Seq<i32>, d: Seq<i32>, i: usize, j: usize, val_d: i32)
    requires
        j < d.len(),
        b.subrange(0, (i + j) as int).to_multiset() == c.subrange(0, i as int).to_multiset().add(d.subrange(0, j as int).to_multiset()),
        b.len() >= (i + j + 1) as int,
        b[(i+j) as int] == val_d,
        d[j as int] == val_d,
    ensures
        b.subrange(0, (i + j + 1) as int).to_multiset() == c.subrange(0, i as int).to_multiset().add(d.subrange(0, (j + 1) as int).to_multiset()),
{
    assert(b.subrange(0, (i + j + 1) as int).to_multiset() == b.subrange(0, (i + j) as int).to_multiset().add(multiset![b[(i+j) as int]]));
    assert(d.subrange(0, (j + 1) as int).to_multiset() == d.subrange(0, j as int).to_multiset().add(multiset![d[j as int]]));
}

lemma fn sorted_prefix_append(s: Seq<i32>, val: i32, current_len: int)
    requires
        s.len() > current_len,
        s[current_len] == val,
        sorted(s.subrange(0, current_len)),
        current_len == 0 || s[current_len - 1] <= val,
    ensures
        sorted(s.subrange(0, current_len + 1)),
{
    if current_len == 0 {
        assert(sorted(s.subrange(0, 1)));
    } else {
        forall |k: int| 0 <= k < current_len implies #[trigger] s[k] <= s[current_len] by {
            if s[k] <= s[current_len -1] && s[current_len - 1] <= s[current_len] {
                assert (s[k] <= s[current_len]);
            }
        }
        assert(sorted(s.subrange(0, current_len + 1)));
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
    let mut i: usize = 0;
    let mut j: usize = 0;

    while i < c.len() || j < d.len()
        invariant
            i <= c.len(),
            j <= d.len(),
            (i + j) as int <= b.len() as int,
            inv_sub_set(b@, c@, d@, i, j),
            inv_sorted(b@, c@, d@, i, j),
            sorted(c@),
            sorted(d@),
            b.len() == (old(b)).len(),
    {
        if i == c.len() {
            // take from d
            assert(j < d.len());
            let val = d[j];
            b.set(i + j, val);

            proof {
                lemma_add_d_multiset(b@, c@, d@, i, j, val);
                assert(inv_sorted(b@.update((i+j) as int, val), c@, d@, i, j)); // This assertion is crucial to show that if we update b at the correct index this invariant holds
                sorted_prefix_append(b@, val, (i + j) as int);
            }
            j = j + 1;
        } else if j == d.len() {
            // take from c
            assert(i < c.len());
            let val = c[i];
            b.set(i + j, val);

            proof {
                lemma_add_c_multiset(b@, c@, d@, i, j, val);
                assert(inv_sorted(b@.update((i+j) as int, val), c@, d@, i, j));
                sorted_prefix_append(b@, val, (i + j) as int);
            }
            i = i + 1;
        } else if c[i] <= d[j] {
            // take from c
            let val = c[i];
            b.set(i + j, val);

            proof {
                lemma_add_c_multiset(b@, c@, d@, i, j, val);
                assert(inv_sorted(b@.update((i+j) as int, val), c@, d@, i, j));
                sorted_prefix_append(b@, val, (i + j) as int);
            }
            i = i + 1;
        } else {
            // take from d
            let val = d[j];
            b.set(i + j, val);

            proof {
                lemma_add_d_multiset(b@, c@, d@, i, j, val);
                assert(inv_sorted(b@.update((i+j) as int, val), c@, d@, i, j));
                sorted_prefix_append(b@, val, (i + j) as int);
            }
            j = j + 1;
        }
    }

    assert(i == c.len());
    assert(j == d.len());
    let final_len = i + j;
    assert(final_len == c.len() + d.len());
    assert(final_len == b.len());
    assert(inv_sub_set(b@, c@, d@, i, j));
    assert(inv_sorted(b@, c@, d@, i, j));

    proof {
        muliset_eq(b@, c@, d@);
    }
    assert(sorted(b@));
}
// </vc-code>

fn main() {}

}