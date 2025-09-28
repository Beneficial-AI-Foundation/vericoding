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
// Helper lemma to prove that concatenating sorted sequences preserves multisets
proof fn lemma_concat_multiset(a: Seq<int>, b: Seq<int>, c: Seq<int>)
    requires
        a.len() == b.len() + c.len(),
        a =~= b + c,
    ensures
        a.to_multiset() == b.to_multiset().add(c.to_multiset()),
{
    assert forall |x: int| #[trigger] a.to_multiset().count(x) == 
        b.to_multiset().count(x) + c.to_multiset().count(x) by {
        let count_a = a.filter(|y: int| y == x).len();
        let count_b = b.filter(|y: int| y == x).len();
        let count_c = c.filter(|y: int| y == x).len();
        assert(count_a == count_b + count_c);
    }
}

// Helper lemma to prove that splitting and recombining preserves multisets
proof fn lemma_split_multiset(a: Seq<int>, mid: int)
    requires
        0 <= mid <= a.len(),
    ensures
        a.to_multiset() == a.subrange(0, mid).to_multiset().add(a.subrange(mid, a.len() as int).to_multiset()),
{
    let left = a.subrange(0, mid);
    let right = a.subrange(mid, a.len() as int);
    assert(a =~= left + right);
    lemma_concat_multiset(a, left, right);
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
    
    // Split the array into two halves
    let mut left: Vec<int> = Vec::new();
    let mut right: Vec<int> = Vec::new();
    
    let ghost orig_a = a@;
    
    // Copy first half to left
    let mut i = 0;
    while i < mid
        invariant
            i <= mid,
            left@.len() == i,
            forall |k: int| 0 <= k < i ==> #[trigger] left@[k] == a@[k],
            left@ =~= a@.subrange(0, i as int),
    {
        left.push(a[i]);
        i = i + 1;
    }
    
    // Copy second half to right
    let mut j = mid;
    while j < a.len()
        invariant
            mid <= j <= a.len(),
            right@.len() == j - mid,
            forall |k: int| 0 <= k < j - mid ==> #[trigger] right@[k] == a@[mid + k],
            right@ =~= a@.subrange(mid as int, j as int),
    {
        right.push(a[j]);
        j = j + 1;
    }
    
    assert(left@ =~= orig_a.subrange(0, mid as int));
    assert(right@ =~= orig_a.subrange(mid as int, orig_a.len() as int));
    
    // Recursively sort both halves
    let sorted_left = merge_sort(left);
    let sorted_right = merge_sort(right);
    
    // Create result vector with proper capacity
    let mut result: Vec<int> = Vec::with_capacity(a.len());
    let mut k = 0;
    while k < a.len()
        invariant
            k <= a.len(),
            result@.len() == k,
    {
        result.push(0); // Fixed: use plain 0 for int literal
        k = k + 1;
    }
    
    proof {
        lemma_split_multiset(orig_a, mid as int);
        assert(orig_a.to_multiset() == 
            orig_a.subrange(0, mid as int).to_multiset().add(
                orig_a.subrange(mid as int, orig_a.len() as int).to_multiset()));
    }
    
    // Merge the sorted halves
    merge(&mut result, &sorted_left, &sorted_right);
    
    result
}
// </vc-code>

fn main() {}

}