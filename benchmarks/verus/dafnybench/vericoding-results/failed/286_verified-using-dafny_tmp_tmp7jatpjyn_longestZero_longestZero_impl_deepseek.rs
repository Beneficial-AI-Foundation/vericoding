use vstd::prelude::*;

verus! {

spec fn get_size(i: int, j: int) -> int {
    j - i + 1
}

// For a given integer array, let's find the longest subsequence of 0s.
// sz: size, pos: position. a[pos..(pos+sz)] will be all zeros

// <vc-helpers>
spec fn is_zero_run(a: Seq<i32>, start: int, end: int) -> bool
    recommends 0 <= start <= end < a.len()
{
    forall |k: int| start <= k <= end ==> a[k] == 0
}

proof fn zero_run_lemma(a: Seq<i32>, i: int, j: int, max_sz: nat, max_start: int)
    requires
        0 <= max_start,
        max_start + max_sz <= a.len(),
        is_zero_run(a, max_start, max_start + max_sz - 1),
    ensures
        forall |ii: int, jj: int| {
            0 <= ii <= jj < a.len() && (jj - ii + 1) > (max_sz as int)
            ==> exists |k: int| ii <= k <= jj && a[k] != 0
        }
{
    assert forall |ii: int, jj: int| 
        0 <= ii <= jj < a.len() && (jj - ii + 1) > (max_sz as int) 
        implies exists |k: int| ii <= k <= jj && a[k] != 0 by {
        if is_zero_run(a, ii, jj) {
            assert((jj - ii + 1) <= (max_sz as int));
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn longest_zero(a: &[i32]) -> (result: (usize, usize))
    requires 
        1 <= a.len()
    ensures 
        result.0 <= a.len(),
        result.1 < a.len(),
        result.1 + result.0 <= a.len(),
        forall |i: int| result.1 <= i < (result.1 + result.0) ==> a[i as int] == 0,
        forall |i: int, j: int| {
            0 <= i < j < a.len() && get_size(i, j) > (result.0 as int)
            ==> exists |k: int| i <= k <= j && a[k] != 0
        }
// </vc-spec>
// <vc-code>
{
    let mut max_sz: usize = 0;
    let mut max_start: usize = 0;
    let mut current_start: usize = 0;
    let mut in_zero_run = false;
    let n = a.len();
    
    let mut i: usize = 0;
    assert(1 <= n);
    while i < n
        invariant
            0 <= i <= n,
            max_sz <= n,
            max_start <= n,
            max_start + max_sz <= n,
            current_start <= n,
            forall |k: int| max_start as int <= k < max_start as int + max_sz as int ==> 
                a[k] == 0,
            forall |ii: int, jj: int| 
                0 <= ii <= jj < i as int && (jj - ii + 1) > (max_sz as int)
                ==> exists |k: int| ii <= k <= jj && a[k] != 0
        decreases n - i
    {
        if a[i] == 0 {
            if !in_zero_run {
                current_start = i;
                in_zero_run = true;
            }
            let current_sz = i - current_start + 1;
            if current_sz > max_sz {
                max_sz = current_sz;
                max_start = current_start;
            }
        } else {
            in_zero_run = false;
        }
        i += 1;
    }
    
    proof {
        zero_run_lemma(a@, 0, 0, max_sz as nat, max_start as int);
    }
    
    (max_sz, max_start)
}
// </vc-code>

fn main() {}

}