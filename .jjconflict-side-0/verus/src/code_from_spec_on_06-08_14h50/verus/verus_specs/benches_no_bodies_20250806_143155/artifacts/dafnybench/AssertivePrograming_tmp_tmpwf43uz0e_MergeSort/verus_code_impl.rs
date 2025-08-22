use vstd::prelude::*;

verus! {
    // Noa Leron 207131871
    // Tsuri Farhana 315016907

    spec fn sorted(q: Seq<i32>) -> bool {
        forall|i: int, j: int| 0 <= i <= j < q.len() ==> q[i] <= q[j]
    }

    spec fn inv(a: Seq<i32>, a1: Seq<i32>, a2: Seq<i32>, i: nat, mid: nat) -> bool {
        (i <= a1.len()) && (i <= a2.len()) && (i + mid <= a.len()) &&
        (a1.subrange(0, i as int) == a.subrange(0, i as int)) && 
        (a2.subrange(0, i as int) == a.subrange(mid as int, (i + mid) as int))
    }

    /*
    Goal: Implement the well known merge sort algorithm in O(a.Length X log_2(a.Length)) time, recursively.

    - Divide the contents of the original array into two local arrays
    - After sorting the local arrays (recursively), merge the contents of the two returned arrays using the Merge method (see below)
    - DO NOT modify the specification or any other part of the method's signature
    - DO NOT introduce any further methods
    */
    fn merge_sort(a: Vec<i32>) -> (b: Vec<i32>)
        ensures 
            b.len() == a.len(),
            sorted(b@),
            a@.to_multiset() == b@.to_multiset()
        decreases a.len()
    {
        if a.len() <= 1 {
            return a;
        }
        
        let mid = a.len() / 2;
        let mut left = Vec::new();
        let mut right = Vec::new();
        
        for i in 0..mid {
            left.push(a[i]);
        }
        
        for i in mid..a.len() {
            right.push(a[i]);
        }
        
        let sorted_left = merge_sort(left);
        let sorted_right = merge_sort(right);
        
        merge(sorted_left, sorted_right)
    }

    /*
    Goal: Implement iteratively, correctly, efficiently, clearly

    DO NOT modify the specification or any other part of the method's signature
    */
    fn merge(c: Vec<i32>, d: Vec<i32>) -> (b: Vec<i32>)
        requires 
            sorted(c@),
            sorted(d@)
        ensures 
            sorted(b@),
            b@.to_multiset() == c@.to_multiset().add(d@.to_multiset()),
            b.len() == c.len() + d.len()
    {
        let mut b = Vec::new();
        let mut i: usize = 0;
        let mut j: usize = 0;
        
        /* code modified by LLM (iteration 1): added decreases clause to fix compilation error */
        while i < c.len() && j < d.len() 
            invariant
                i <= c.len(),
                j <= d.len(),
                b.len() == i + j,
                inv_sorted_merge(b@, c@, d@, i as int, j as int),
                inv_subset(b@, c@, d@, i as int, j as int)
            decreases c.len() + d.len() - i - j
        {
            if c[i] <= d[j] {
                b.push(c[i]);
                proof {
                    lemma_inv_subset_take_value_from_c(b@, c@, d@, i as int, j as int);
                }
                i += 1;
            } else {
                b.push(d[j]);
                proof {
                    lemma_inv_subset_take_value_from_d(b@, c@, d@, i as int, j as int);
                }
                j += 1;
            }
        }
        
        while i < c.len()
            invariant
                i <= c.len(),
                j == d.len(),
                b.len() == i + j,
                inv_sorted_merge(b@, c@, d@, i as int, j as int),
                inv_subset(b@, c@, d@, i as int, j as int)
            decreases c.len() - i
        {
            b.push(c[i]);
            proof {
                lemma_inv_subset_take_value_from_c(b@, c@, d@, i as int, j as int);
            }
            i += 1;
        }
        
        while j < d.len()
            invariant
                i == c.len(),
                j <= d.len(),
                b.len() == i + j,
                inv_sorted_merge(b@, c@, d@, i as int, j as int),
                inv_subset(b@, c@, d@, i as int, j as int)
            decreases d.len() - j
        {
            b.push(d[j]);
            proof {
                lemma_inv_subset_take_value_from_d(b@, c@, d@, i as int, j as int);
            }
            j += 1;
        }
        
        proof {
            lemma_multisets_equals(b@, c@, d@, i as int, j as int);
        }
        
        b
    }

    // Loop invariant - b is sorted so far and the next two potential values that will go into b are bigger than the biggest value in b.
    spec fn inv_sorted_merge(b: Seq<i32>, c: Seq<i32>, d: Seq<i32>, i: int, j: int) -> bool {
        i <= c.len() && j <= d.len() && i + j <= b.len() &&
        ((i + j > 0 && i < c.len()) ==> (b[j + i - 1] <= c[i])) &&
        ((i + j > 0 && j < d.len()) ==> (b[j + i - 1] <= d[j])) &&
        sorted(b.subrange(0, i + j))
    }

    // Loop invariant - the multiset of the prefix of b so far is the same multiset as the prefixes of c and d so far.
    spec fn inv_subset(b: Seq<i32>, c: Seq<i32>, d: Seq<i32>, i: int, j: int) -> bool {
        i <= c.len() && j <= d.len() && i + j <= b.len() &&
        b.subrange(0, i + j).to_multiset() == c.subrange(0, i).to_multiset().add(d.subrange(0, j).to_multiset())
    }

    // This lemma helps prove that if the prefixes of arrays are the same multiset until the end of the arrays,
    // all the arrays are the same multiset.
    proof fn lemma_multisets_equals(b: Seq<i32>, c: Seq<i32>, d: Seq<i32>, i: int, j: int)
        requires 
            i == c.len(),
            j == d.len(),
            i + j == b.len(),
            b.subrange(0, i+j).to_multiset() == c.subrange(0, i).to_multiset().add(d.subrange(0, j).to_multiset())
        ensures b.to_multiset() == c.to_multiset().add(d.to_multiset())
    {
        assert(b == b.subrange(0, i+j));
        assert(c == c.subrange(0, i));
        assert(d == d.subrange(0, j));
    }

    // This lemma helps prove that after adding the next value from c to b the prefixes are still the same subsets.
    proof fn lemma_inv_subset_take_value_from_c(b: Seq<i32>, c: Seq<i32>, d: Seq<i32>, i: int, j: int)
        requires 
            i < c.len(),
            j <= d.len(),
            i + j < b.len(),
            c.len() + d.len() == b.len(),
            b.subrange(0, i+j).to_multiset() == c.subrange(0, i).to_multiset().add(d.subrange(0, j).to_multiset()),
            b[i+j] == c[i]
        ensures b.subrange(0, i+j+1).to_multiset() == c.subrange(0, i+1).to_multiset().add(d.subrange(0, j).to_multiset())
    {
        assert(c.subrange(0, i) + seq![c[i]] == c.subrange(0, i+1));
        assert(b.subrange(0, i+j+1) == b.subrange(0, i+j) + seq![b[i+j]]);
    }

    // This lemma helps prove that after adding the next value from d to b the prefixes are still the same subsets.
    proof fn lemma_inv_subset_take_value_from_d(b: Seq<i32>, c: Seq<i32>, d: Seq<i32>, i: int, j: int)
        requires 
            i <= c.len(),
            j < d.len(),
            i + j < b.len(),
            c.len() + d.len() == b.len(),
            b.subrange(0, i+j).to_multiset() == c.subrange(0, i).to_multiset().add(d.subrange(0, j).to_multiset()),
            b[i+j] == d[j]
        ensures b.subrange(0, i+j+1).to_multiset() == c.subrange(0, i).to_multiset().add(d.subrange(0, j+1).to_multiset())
    {
        assert(d.subrange(0, j) + seq![d[j]] == d.subrange(0, j+1));
        assert(b.subrange(0, i+j+1) == b.subrange(0, i+j) + seq![b[i+j]]);
    }

    fn main() {
        let test_vec = vec![3, 1, 4, 1, 5, 9, 2, 6];
        let sorted_vec = merge_sort(test_vec);
        /* code modified by LLM (iteration 1): removed println! as it's not supported in Verus */
        // println!("Sorted vector: {:?}", sorted_vec);
    }
}