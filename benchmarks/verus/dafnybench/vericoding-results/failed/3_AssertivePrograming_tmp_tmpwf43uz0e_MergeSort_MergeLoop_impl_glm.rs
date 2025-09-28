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
proof fn lemma_prefix_multiset(
    b: Seq<int>, c: Seq<int>, d: Seq<int>,
    i: nat, j: nat, i_new: nat, j_new: nat,
) {
    requires(inv_sub_set(b, c, d, i, j));
    requires(
        i_new == i + 1 && j_new == j && i_new <= c.len() && j_new <= d.len() && 
        i_new + j_new <= b.len()
    );
    ensures(inv_sub_set(b, c, d, i_new, j_new));
}

proof fn lemma_prefix_sorted(
    b: Seq<int>, c: Seq<int>, d: Seq<int>,
    i: nat, j: nat, i_new: nat, j_new: nat,
    val: int,
) {
    requires(inv_sorted(b, c, d, i, j));
    requires(
        (i < c.len() && j < d.len() && c[i as int] <= d[j as int] && i_new == i + 1 && j_new == j) ||
        (j < d.len() && (i >= c.len() || c[i as int] > d[j as int]) && i_new == i && j_new == j + 1)
    );
    requires(i_new <= c.len() && j_new <= d.len() && i_new + j_new <= b.len());
    requires(
        (i_new + j_new > 0 && i_new < c.len()) ==> val <= c[i_new as int]
    );
    requires(
        (i_new + j_new > 0 && j_new < d.len()) ==> val <= d[j_new as int]
    );
    ensures(inv_sorted(b, c, d, i_new, j_new));
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
    
    while i + j < b.len()
        invariant
            i <= c.len(),
            j <= d.len(),
            i + j <= b.len(),
            inv_sub_set(b@, c@, d@, i as nat, j as nat),
            inv_sorted(b@, c@, d@, i as nat, j as nat),
    {
        if i < c.len() && (j >= d.len() || c[i] <= d[j]) {
            let val = c[i];
            b[i + j] = val;
            let i_new = i + 1;
            let j_new = j;
            
            assert(i_new <= c.len() && j_new <= d.len() && i_new + j_new <= b.len());
            
            proof {
                lemma_prefix_multiset(b@, c@, d@, i as nat, j as nat, i_new as nat, j_new as nat);
            }
            
            if i_new + j_new > 0 && i_new < c.len() {
                assert(i + j > 0);
                assert(b@[(i + j - 1) as int] == val);
                assert(val <= c[i_new as int]);
            }
            if i_new + j_new > 0 && j_new < d.len() {
                assert(i + j > 0);
                assert(b@[(i + j - 1) as int] == val);
                if i < c.len() {
                    assert(val <= c[i as int] && c[i as int] <= d[j as int]);
                }
                if i >= c.len() {
                    assert(j < d.len());
                    assert(val == d[j as int] && j < j_new);
                    assert(sorted(d@.subrange(0, (j_new) as int)));
                    assert(d@[j as int] <= d@[j_new as int]);
                }
            }
            
            proof {
                lemma_prefix_sorted(b@, c@, d@, i as nat, j as nat, i_new as nat, j_new as nat, val);
            }
            
            i = i_new;
        } else {
            assert(j < d.len() && (i >= c.len() || c[i] > d[j]));
            let val = d[j];
            b[i + j] = val;
            let i_new = i;
            let j_new = j + 1;
            
            assert(i_new <= c.len() && j_new <= d.len() && i_new + j_new <= b.len());
            
            proof {
                lemma_prefix_multiset(b@, c@, d@, i as nat, j as nat, i_new as nat, j_new as nat);
            }
            
            if i_new + j_new > 0 && i_new < c.len() {
                assert(i + j > 0);
                assert(b@[(i + j - 1) as int] == val);
                if i < c.len() {
                    assert(val < c[i as int]);
                }
                if i >= c.len() {
                    assert(j + 1 == j_new);
                    assert(sorted(c@.subrange(0, (i_new) as int)));
                }
            }
            if i_new + j_new > 0 && j_new < d.len() {
                assert(i + j > 0);
                assert(b@[(i + j - 1) as int] == val);
                assert(val <= d[j_new as int]);
            }
            
            proof {
                lemma_prefix_sorted(b@, c@, d@, i as nat, j as nat, i_new as nat, j_new as nat, val);
            }
            
            j = j_new;
        }
    }
    
    (i, j)
}
// </vc-code>

fn main() {
}

}