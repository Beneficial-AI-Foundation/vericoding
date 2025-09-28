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
proof fn lemma_subrange_concat_single(s: Seq<int>, i: nat)
    requires
        i < s.len(),
    ensures
        s.subrange(0, (i + 1) as int).to_multiset() =~= s.subrange(0, i as int).to_multiset().add(s.subrange(i as int, (i + 1) as int).to_multiset())
{
    // s[0..i+1) == s[0..i) ++ s[i..i+1)
    assert(s.subrange(0, (i + 1) as int) =~= s.subrange(0, i as int).concat(s.subrange(i as int, (i + 1) as int)));
    // to_multiset of concat is add of multisets
    assert(s.subrange(0, i as int).concat(s.subrange(i as int, (i + 1) as int)).to_multiset() =~= s.subrange(0, i as int).to_multiset().add(s.subrange(i as int, (i + 1) as int).to_multiset()));
    assert(s.subrange(0, (i + 1) as int).to_multiset() =~= s.subrange(0, i as int).to_multiset().add(s.subrange(i as int, (i + 1) as int).to_multiset()));
}

proof fn lemma_sorted_adj(s: Seq<int>, i: nat)
    requires
        sorted(s),
        i + 1 < s.len(),
    ensures
        s[i as int] <= s[(i + 1) as int]
{
    // instantiate sorted for consecutive indices
    assert(s[i as int] <= s[(i + 1) as int]);
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
            0 <= c.len() - r.0 < c.len() - i0 || (c.len() - r.0 == c.len() - i0 && 0 <= d.len() - r.1 < d.len() - j0)
{
    let mut i: usize = i0;
    let mut j: usize = j0;

    // Loop until we've filled all positions of b (i + j == b.len())
    while i + j < b.len()
        invariant i <= c.len()
        invariant j <= d.len()
        invariant i + j <= b.len()
        invariant b@.subrange(0, (i + j) as int).to_multiset() =~= c@.subrange(0, i as int).to_multiset().add(d@.subrange(0, j as int).to_multiset())
        invariant sorted(b@.subrange(0, (i + j) as int))
        invariant ((i + j > 0 && i < c.len()) ==> (b@[(j + i - 1) as int] <= c@[i as int]))
        invariant ((i + j > 0 && j < d.len()) ==> (b@[(j + i - 1) as int] <= d@[j as int]))
        decreases (c.len() - i) + (d.len() - j)
    {
        let k = i + j;
        if i < c.len() && j < d.len() {
            if c@[i as int] <= d@[j as int] {
                // place c[i] into b[k]
                b[k] = c@[i as int];
                // update invariants
                proof {
                    // multiset: extend b's prefix by singleton b[k] which equals c[i]
                    assert(b@.subrange(0, k as int).to_multiset() =~= c@.subrange(0, i as int).to_multiset().add(d@.subrange(0, j as int).to_multiset()));
                    assert(b@.subrange(0, (k + 1) as int).to_multiset() =~= b@.subrange(0, k as int).to_multiset().add(b@.subrange(k as int, (k + 1) as int).to_multiset()));
                    assert(b@[k as int] == c@[i as int]);
                    assert(b@.subrange(k as int, (k + 1) as int).to_multiset() =~= c@.subrange(i as int, (i + 1) as int).to_multiset());
                    // combine: previous multiset plus c[i] equals c[0..i+1) + d[0..j)
                    lemma_subrange_concat_single(c@, i as nat);
                    assert(b@.subrange(0, (k + 1) as int).to_multiset() =~= c@.subrange(0, (i + 1) as int).to_multiset().add(d@.subrange(0, j as int).to_multiset()));
                    // sorted: previous sorted prefix and last <= c[i] imply new sorted prefix
                    assert(sorted(b@.subrange(0, k as int)));
                    if k > 0 {
                        assert(b@[(k - 1) as int] <= c@[i as int]);
                    }
                    assert(sorted(b@.subrange(0, (k + 1) as int)));
                    // maintain comparison invariants for next iteration:
                    // for c: need b[k] <= c[i+1] when i+1 < c.len()
                    if i + 1 < c.len() {
                        lemma_sorted_adj(c@, i as nat);
                        assert(b@[(k) as int] == c@[i as int]);
                        assert(b@[(k) as int] <= c@[(i + 1) as int]);
                    }
                    // for d: need b[k] <= d[j] when j < d.len()
                    if j < d.len() {
                        assert(b@[(k) as int] == c@[i as int]);
                        assert(c@[i as int] <= d@[j as int]);
                        assert(b@[(k) as int] <= d@[j as int]);
                    }
                }
                i += 1;
            } else {
                // place d[j] into b[k]
                b[k] = d@[j as int];
                proof {
                    assert(b@.subrange(0, k as int).to_multiset() =~= c@.subrange(0, i as int).to_multiset().add(d@.subrange(0, j as int).to_multiset()));
                    assert(b@.subrange(0, (k + 1) as int).to_multiset() =~= b@.subrange(0, k as int).to_multiset().add(b@.subrange(k as int, (k + 1) as int).to_multiset()));
                    assert(b@[k as int] == d@[j as int]);
                    assert(b@.subrange(k as int, (k + 1) as int).to_multiset() =~= d@.subrange(j as int, (j + 1) as int).to_multiset());
                    lemma_subrange_concat_single(d@, j as nat);
                    assert(b@.subrange(0, (k + 1) as int).to_multiset() =~= c@.subrange(0, i as int).to_multiset().add(d@.subrange(0, (j + 1) as int).to_multiset()));
                    // sorted: previous sorted prefix and last <= d[j] imply new sorted prefix
                    assert(sorted(b@.subrange(0, k as int)));
                    if k > 0 {
                        assert(b@[(k - 1) as int] <= d@[j as int]);
                    }
                    assert(sorted(b@.subrange(0, (k + 1) as int)));
                    // maintain comparison invariants for next iteration:
                    // for d: need b[k] <= d[j+1] when j+1 < d.len()
                    if j + 1 < d.len() {
                        lemma_sorted_adj(d@, j as nat);
                        assert(b@[(k) as int] == d@[j as int]);
                        assert(b@[(k) as int] <= d@[(j + 1) as int]);
                    }
                    // for c: need b[k] <= c[i] when i < c.len()
                    if i < c.len() {
                        assert(b@[(k) as int] == d@[j as int]);
                        assert(d@[j as int] <= c@[i as int]);
                        assert(b@[(k) as int] <= c@[i as int]);
                    }
                }
                j += 1;
            }
        } else if i < c.len() {
            // only c remains
            b[k] = c@[i as int];
            proof {
                assert(b@.subrange(0, k as int).to_multiset() =~= c@.subrange(0, i as int).to_multiset().add(d@.subrange(0, j as int).to_multiset()));
                assert(b@.subrange(0, (k + 1) as int).to_multiset() =~= b@.subrange(0, k as int).to_multiset().add(b@.subrange(k as int, (k + 1) as int).to_multiset()));
                assert(b@[k as int] == c@[i as int]);
                assert(b@.subrange(k as int, (k + 1) as int).to_multiset() =~= c@.subrange(i as int, (i + 1) as int).to_multiset());
                lemma_subrange_concat_single(c@, i as nat);
                assert(b@.subrange(0, (k + 1) as int).to_multiset() =~= c@.subrange(0, (i + 1) as int).to_multiset().add(d@.subrange(0, j as int).to_multiset()));
                assert(sorted(b@.subrange(0, k as int)));
                if k > 0 {
                    assert(b@[(k - 1) as int] <= c@[i as int]);
                }
                assert(sorted(b@.subrange(0, (k + 1) as int)));
                // maintain comparison invariant for c: b[k] <= c[i+1] if i+1 < c.len()
                if i + 1 < c.len() {
                    lemma_sorted_adj(c@, i as nat);
                    assert(b@[(k) as int] == c@[i as int]);
                    assert(b@[(k) as int] <= c@[(i + 1) as int]);
                }
            }
            i += 1;
        } else {
            // only d remains
            b[k] = d@[j as int];
            proof {
                assert(b@.subrange(0, k as int).to_multiset() =~= c@.subrange(0, i as int).to_multiset().add(d@.subrange(0, j as int).to_multiset()));
                assert(b@.subrange(0, (k + 1) as int).to_multiset() =~= b@.subrange(0, k as int).to_multiset().add(b@.subrange(k as int, (k + 1) as int).to_multiset()));
                assert(b@[k as int] == d@[j as int]);
                assert(b@.subrange(k as int, (k + 1) as int).to_multiset() =~= d@.subrange(j as int, (j + 1) as int).to_multiset());
                lemma_subrange_concat_single(d@, j as nat);
                assert(b@.subrange(0, (k + 1) as int).to_multiset() =~= c@.subrange(0, i as int).to_multiset().add(d@.subrange(0, (j + 1) as int).to_multiset()));
                assert(sorted(b@.subrange(0, k as int)));
                if k > 0 {
                    assert(b@[(k - 1) as int] <= d@[j as int]);
                }
                assert(sorted(b@.subrange(0, (k + 1) as int)));
                // maintain comparison invariant for d: b[k] <= d[j+1] if j+1 < d.len()
                if j + 1 < d.len() {
                    lemma_sorted_adj(d@, j as nat);
                    assert(b@[(k) as int] == d@[j as int]);
                    assert(b@[(k) as int] <= d@[(j + 1) as int]);
                }
            }
            j += 1;
        }
    }

    // After loop: i + j == b.len()
    proof {
        assert(i + j == b.len());
        // relate b.len() with old(b).len() (length unchanged)
        assert(b.len() == old(b).len());
        assert(i + j == old(b).len());
        assert(old(b).len() == c.len() + d.len());
        assert(i + j == c.len() + d.len());

        // from i <= c.len() and j <= d.len() and i + j == c.len() + d.len() deduce i == c.len() and j == d.len()
        assert(i >= c.len());
        assert(i <= c.len());
        assert(i == c.len());
        assert(j >= d.len());
        assert(j <= d.len());
        assert(j == d.len());

        // Now prove the final decreasing ensures
        // c.len() - i == 0
        assert(c.len() - i == 0);
        if c.len() - i0 > 0 {
            // first disjunct holds: 0 <= c.len()-i < c.len()-i0
            assert(0 <= c.len() - i);
            assert(c.len() - i < c.len() - i0);
        } else {
            // c.len() - i0 == 0, so i0 == c.len()
            assert(c.len() - i0 == 0);
            // need second disjunct: 0 <= d.len() - j < d.len() - j0
            assert(0 <= d.len() - j);
            // d.len() - j == 0
            assert(d.len() - j == 0);
            // since i0 + j0 < old(b).len() and i0 == c.len(), we have j0 < d.len()
            assert(i0 == c.len());
            assert(i0 + j0 < old(b).len());
            assert(j0 < d.len());
            assert(d.len() - j0 > 0);
            assert(d.len() - j < d.len() - j0);
        }
    }

    return (i, j);
}
}
// </vc-code>

fn main() {
}

}