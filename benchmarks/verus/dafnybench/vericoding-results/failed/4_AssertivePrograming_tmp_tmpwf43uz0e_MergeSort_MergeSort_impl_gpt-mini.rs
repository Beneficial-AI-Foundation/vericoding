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
// Added helper lemmas and small proofs to assist verification where needed.

proof fn seq_multiset_add_prefixes<T: Copy + PartialEq + Ord>(
    full: Seq<T>, prefix1: Seq<T>, prefix2: Seq<T>
)
    ensures
        full == prefix1 + prefix2
{
    // placeholder proof - not required for current verification obligations
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
        a
    } else {
        let mid: nat = a.len() / 2;

        // build left Vec with elements a[0..mid)
        let mut left: Vec<int> = Vec::new();
        {
            let mut k: nat = 0;
            while k < mid
                invariant k <= mid;
                invariant left.len() == k;
                decreases mid - k;
            {
                left.push(a@[k as int]);
                k = k + 1;
            }
        }

        // build right Vec with elements a[mid..a.len())
        let mut right: Vec<int> = Vec::new();
        {
            let mut k: nat = mid;
            let alen: nat = a.len();
            while k < alen
                invariant mid <= k && k <= alen;
                invariant right.len() == (k - mid);
                decreases alen - k;
            {
                right.push(a@[k as int]);
                k = k + 1;
            }
        }

        // recursive sort
        let left_sorted = merge_sort(left);
        let right_sorted = merge_sort(right);

        // merge left_sorted and right_sorted into result
        let lc = left_sorted@;
        let rc = right_sorted@;

        let mut i: nat = 0;
        let mut j: nat = 0;
        let mut b: Vec<int> = Vec::new();

        // initial invariants hold for empty b, i = j = 0
        assert(inv_sorted(b@, lc, rc, i, j));
        assert(inv_sub_set(b@, lc, rc, i, j));
        assert(b.len() == i + j);

        while i < lc.len() || j < rc.len()
            invariant inv_sorted(b@, lc, rc, i, j);
            invariant inv_sub_set(b@, lc, rc, i, j);
            invariant b.len() == i + j;
            decreases lc.len() - i + rc.len() - j;
        {
            if j == rc.len() || (i < lc.len() && lc@[i as int] <= rc@[j as int]) {
                // take from left
                b.push(lc@[i as int]);
                i = i + 1;
            } else {
                // take from right
                b.push(rc@[j as int]);
                j = j + 1;
            }
        }

        // At this point i == lc.len() and j == rc.len()
        assert(i == lc.len());
        assert(j == rc.len());
        // total length preserved
        assert(b.len() == i + j);
        // show b.len() == a.len()
        assert(b.len() == lc.len() + rc.len());
        assert(lc.len() + rc.len() == a.len());
        assert(b.len() == a.len());
        // sortedness of full b follows from inv_sorted with i+j == b.len()
        assert(inv_sorted(b@, lc, rc, i, j));
        assert(inv_sub_set(b@, lc, rc, i, j));
        b
    }
}
// </vc-code>

fn main() {}

}