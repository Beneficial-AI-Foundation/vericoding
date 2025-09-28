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
proof fn lemma_sorted_prefix_extension(s: Seq<int>, i: int, val: int)
    requires
        sorted(s.subrange(0, i)),
        i > 0,
        s[i - 1] <= val,
    ensures
        sorted(s.subrange(0, i).push(val)),
{
}

proof fn lemma_multiset_prefix_extension<A>(s: Seq<A>, val: A, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        s.subrange(0, i).push(val).to_multiset() =~= s.subrange(0, i).to_multiset().add(vstd::multiset::Multiset::singleton(val)),
{
}

proof fn lemma_multiset_add_commutative<A>(s1: vstd::multiset::Multiset<A>, s2: vstd::multiset::Multiset<A>, s3: vstd::multiset::Multiset<A>)
    ensures
        s1.add(s2).add(s3) =~= s1.add(s3).add(s2),
{
}

proof fn lemma_multiset_eq_subrange<A>(s1: Seq<A>, s2: Seq<A>, start: int, end: int)
    requires
        0 <= start <= end <= s1.len(),
        0 <= start <= end <= s2.len(),
        s1.subrange(start, end) =~= s2.subrange(start, end),
    ensures
        s1.to_multiset() =~= s2.to_multiset(),
{
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
    let mut left = Vec::new();
    let mut right = Vec::new();
    
    proof {
        assert(a@.subrange(0, mid as int).to_multiset().add(a@.subrange(mid as int, a.len() as int).to_multiset()) =~= a@.to_multiset());
    }
    
    let mut i = 0;
    while i < mid
        invariant
            i <= mid,
            left@ =~= a@.subrange(0, i as int),
            left@.to_multiset() =~= a@.subrange(0, i as int).to_multiset(),
    {
        left.push(a[i]);
        i += 1;
    }
    
    let mut j = mid;
    while j < a.len()
        invariant
            j <= a.len(),
            right@ =~= a@.subrange(mid as int, j as int),
            right@.to_multiset() =~= a@.subrange(mid as int, j as int).to_multiset(),
    {
        right.push(a[j]);
        j += 1;
    }
    
    let sorted_left = merge_sort(left);
    let sorted_right = merge_sort(right);
    
    proof {
        assert(sorted_left@.to_multiset() =~= a@.subrange(0, mid as int).to_multiset());
        assert(sorted_right@.to_multiset() =~= a@.subrange(mid as int, a.len() as int).to_multiset());
    }
    
    let mut merged = Vec::<int>::with_capacity(a.len());
    
    let mut i: usize = 0;
    let mut j: usize = 0;
    
    while i < sorted_left.len() && j < sorted_right.len()
        invariant
            i <= sorted_left.len(),
            j <= sorted_right.len(),
            merged@.to_multiset() =~= sorted_left@.subrange(0, i as int).to_multiset().add(sorted_right@.subrange(0, j as int).to_multiset()),
            sorted(merged@),
    {
        if sorted_left[i] <= sorted_right[j] {
            merged.push(sorted_left[i]);
            proof {
                lemma_sorted_prefix_extension(merged@, merged.len() as int, sorted_left[i] as int);
            }
            i += 1;
        } else {
            merged.push(sorted_right[j]);
            proof {
                lemma_sorted_prefix_extension(merged@, merged.len() as int, sorted_right[j] as int);
            }
            j += 1;
        }
    }
    
    while i < sorted_left.len()
        invariant
            i <= sorted_left.len(),
            j == sorted_right.len(),
            merged@.to_multiset() =~= sorted_left@.subrange(0, i as int).to_multiset().add(sorted_right@.to_multiset()),
            sorted(merged@),
    {
        merged.push(sorted_left[i]);
        proof {
            lemma_sorted_prefix_extension(merged@, merged.len() as int, sorted_left[i] as int);
        }
        i += 1;
    }
    
    while j < sorted_right.len()
        invariant
            j <= sorted_right.len(),
            i == sorted_left.len(),
            merged@.to_multiset() =~= sorted_left@.to_multiset().add(sorted_right@.subrange(0, j as int).to_multiset()),
            sorted(merged@),
    {
        merged.push(sorted_right[j]);
        proof {
            lemma_sorted_prefix_extension(merged@, merged.len() as int, sorted_right[j] as int);
        }
        j += 1;
    }
    
    proof {
        assert(merged@.to_multiset() =~= sorted_left@.to_multiset().add(sorted_right@.to_multiset()));
        assert(sorted_left@.to_multiset().add(sorted_right@.to_multiset()) =~= a@.to_multiset());
    }
    
    merged
}
// </vc-code>

fn main() {}

}