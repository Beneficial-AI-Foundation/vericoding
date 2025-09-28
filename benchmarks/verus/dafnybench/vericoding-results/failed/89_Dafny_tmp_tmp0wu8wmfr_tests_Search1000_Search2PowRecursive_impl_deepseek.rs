use vstd::prelude::*;

verus! {

// Author: Snorri Agnarsson, snorri@hi.is

// Search1000 is a Dafny version of a function shown
// by Jon Bentley in his old Programming Pearls
// column in CACM.  Surprisingly Dafny needs no help
// to verify the function.

// Is2Pow(n) is true iff n==2^k for some k>=0.
spec fn is_2_pow(n: int) -> bool
    decreases n
{
    if n < 1 {
        false
    } else if n == 1 {
        true
    } else {
        n % 2 == 0 && is_2_pow(n / 2)
    }
}

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.

// <vc-helpers>
spec fn is_2_pow_minus_one(n: int) -> bool
    decreases n
{
    if n < 0 {
        false
    } else if n == 0 {
        true
    } else {
        (n + 1) % 2 == 0 && is_2_pow((n + 1) / 2)
    }
}

proof fn lemma_is_2_pow_minus_one_properties(n: int)
    requires
        is_2_pow_minus_one(n),
    ensures
        n >= 0,
        is_2_pow(n + 1),
    decreases n
{
    if n == 0 {
        assert(is_2_pow(1));
    } else {
        assert((n + 1) % 2 == 0);
        assert(is_2_pow((n + 1) / 2));
    }
}

proof fn lemma_binary_search_step(a: Seq<i32>, i: int, n: int, x: i32, mid: int)
    requires
        i + n <= a.len(),
        forall|p: int, q: int| 
            0 <= p < q && i <= p && q < i + n ==> 
            a[p] <= a[q],
        is_2_pow(n + 1),
        mid == i + (n / 2),
    ensures
        i <= mid < i + n,
        (a[mid] < x ==> forall|r: int| i <= r <= mid ==> a[r] <= a[mid] < x),
        (a[mid] >= x ==> forall|r: int| mid <= r < i + n ==> a[r] >= a[mid] >= x)
{
    assert(mid >= i) by {
        assert(n >= 0);
        assert(n / 2 >= 0);
    };
    assert(mid < i + n) by {
        assert(n > 0);
        assert(n / 2 < n);
    };
    
    if a[mid] < x {
        assert forall|r: int| i <= r <= mid implies a[r] <= a[mid] < x by {
            if i <= r <= mid {
                assert(a[r] <= a[mid]);
            }
        };
    } else {
        assert forall|r: int| mid <= r < i + n implies a[r] >= a[mid] >= x by {
            if mid <= r < i + n {
                assert(a[mid] <= a[r]);
            }
        };
    }
}

proof fn lemma_array_slice_sorted(a: Seq<i32>, start: int, end: int, new_start: int, new_end: int)
    requires
        start <= new_start,
        new_end <= end,
        forall|p: int, q: int| 
            0 <= p < q && start <= p && q < end ==> 
            a[p] <= a[q],
    ensures
        forall|p: int, q: int| 
            0 <= p < q && new_start <= p && q < new_end ==> 
            a[p] <= a[q]
{
}
// </vc-helpers>

// <vc-spec>
fn search_2_pow_recursive(a: &[i32], i: usize, n: usize, x: i32) -> (k: usize)
    decreases n
    requires
        i + n <= a.len(),
        forall|p: int, q: int| 
            0 <= p < q && i as int <= p && q < (i + n) as int ==> 
            a[p] <= a[q],
        is_2_pow((n + 1) as int),
    ensures
        i <= k <= i + n,
        forall|r: int| 
            0 <= r && i as int <= r < k as int ==> 
            a[r] < x,
        forall|r: int| 
            0 <= r && k as int <= r < (i + n) as int ==> 
            a[r] >= x,
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        i
    } else {
        let mid = i + n / 2;
        proof {
            lemma_is_2_pow_minus_one_properties(n as int);
        }
        
        if a[mid] < x {
            let new_n = n / 2;
            proof {
                lemma_array_slice_sorted(a@, i as int, (i + n) as int, (mid + 1) as int, (i + n) as int);
            }
            let k = search_2_pow_recursive(a, mid + 1, new_n, x);
            proof {
                assert(i <= k);
                assert(k <= i + n);
                assert forall|r: int| 
                    i as int <= r < k as int implies a[r] < x by {
                    if r < mid as int {
                        lemma_binary_search_step(a@, i as int, n as int, x, mid as int);
                        assert(a[r] <= a[mid as int] < x);
                    } else if r == mid as int {
                        assert(a[r] < x);
                    } else {
                        assert(a[r] < x);
                    }
                };
                assert forall|r: int| 
                    k as int <= r < (i + n) as int implies a[r] >= x;
            }
            k
        } else {
            let new_n = n / 2;
            proof {
                lemma_array_slice_sorted(a@, i as int, (i + n) as int, i as int, (mid) as int);
            }
            let k = search_2_pow_recursive(a, i, new_n, x);
            proof {
                assert(i <= k);
                assert(k <= i + new_n);
                assert forall|r: int| 
                    i as int <= r < k as int implies a[r] < x;
                assert forall|r: int| 
                    k as int <= r < (i + n) as int implies a[r] >= x by {
                    if r < mid as int {
                        assert(a[r] >= x);
                    } else {
                        lemma_binary_search_step(a@, i as int, n as int, x, mid as int);
                        assert(a[r] >= a[mid as int] >= x);
                    }
                };
            }
            k
        }
    }
}
// </vc-code>

fn main() {}

}