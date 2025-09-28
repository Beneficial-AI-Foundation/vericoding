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
proof fn lemma_multiset_add_eq<A>(s1: Seq<A>, s2: Seq<A>, s3: Seq<A>)
    ensures
        s1.to_multiset() =~= s2.to_multiset().add(s3.to_multiset()) ==> 
        forall|x: A| s1.push(x).to_multiset() =~= s2.push(x).to_multiset().add(s3.to_multiset()),
{
}

proof fn lemma_sorted_extension(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat, val: int)
    requires
        inv_sorted(b, c, d, i, j),
        i < c.len(),
        (i + j > 0 ==> b[(i + j - 1) as int] <= val),
        val <= c[i as int],
    ensures
        inv_sorted(b.push(val), c, d, i + 1, j),
{
}

proof fn lemma_multiset_extension(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat, val: int)
    requires
        inv_sub_set(b, c, d, i, j),
        i < c.len(),
        val == c[i as int],
    ensures
        inv_sub_set(b.push(val), c, d, i + 1, j),
{
}

proof fn lemma_sorted_extension2(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat, val: int)
    requires
        inv_sorted(b, c, d, i, j),
        j < d.len(),
        (i + j > 0 ==> b[(i + j - 1) as int] <= val),
        val <= d[j as int],
    ensures
        inv_sorted(b.push(val), c, d, i, j + 1),
{
}

proof fn lemma_multiset_extension2(b: Seq<int>, c: Seq<int>, d: Seq<int>, i: nat, j: nat, val: int)
    requires
        inv_sub_set(b, c, d, i, j),
        j < d.len(),
        val == d[j as int],
    ensures
        inv_sub_set(b.push(val), c, d, i, j + 1),
{
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
    
    assert(i + j < b.len());
    
    while i < c.len() && j < d.len()
        invariant
            i <= c.len(),
            j <= d.len(),
            i + j <= b.len(),
            inv_sub_set(b@, c@, d@, i as nat, j as nat),
            inv_sorted(b@, c@, d@, i as nat, j as nat),
            decreases (c.len() - i) + (d.len() - j),
    {
        assert(i + j < b.len());
        
        if c[i] <= d[j] {
            let val = c[i];
            b.set(i + j, c[i]);
            proof {
                lemma_multiset_extension(b@, c@, d@, i as nat, j as nat, val);
                lemma_sorted_extension(b@, c@, d@, i as nat, j as nat, val);
            }
            i = i + 1;
        } else {
            let val = d[j];
            b.set(i + j, d[j]);
            proof {
                lemma_multiset_extension2(b@, c@, d@, i as nat, j as nat, val);
                lemma_sorted_extension2(b@, c@, d@, i as nat, j as nat, val);
            }
            j = j + 1;
        }
    }
    
    while i < c.len()
        invariant
            i <= c.len(),
            j <= d.len(),
            i + j <= b.len(),
            j == d.len(),
            inv_sub_set(b@, c@, d@, i as nat, j as nat),
            inv_sorted(b@, c@, d@, i as nat, j as nat),
            decreases c.len() - i,
    {
        assert(i + j < b.len());
        let val = c[i];
        b.set(i + j, c[i]);
        proof {
            lemma_multiset_extension(b@, c@, d@, i as nat, j as nat, val);
            lemma_sorted_extension(b@, c@, d@, i as nat, j as nat, val);
        }
        i = i + 1;
    }
    
    while j < d.len()
        invariant
            i <= c.len(),
            j <= d.len(),
            i + j <= b.len(),
            i == c.len(),
            inv_sub_set(b@, c@, d@, i as nat, j as nat),
            inv_sorted(b@, c@, d@, i as nat, j as nat),
            decreases d.len() - j,
    {
        assert(i + j < b.len());
        let val = d[j];
        b.set(i + j, d[j]);
        proof {
            lemma_multiset_extension2(b@, c@, d@, i as nat, j as nat, val);
            lemma_sorted_extension2(b@, c@, d@, i as nat, j as nat, val);
        }
        j = j + 1;
    }
    
    (i, j)
}
// </vc-code>

fn main() {
}

}