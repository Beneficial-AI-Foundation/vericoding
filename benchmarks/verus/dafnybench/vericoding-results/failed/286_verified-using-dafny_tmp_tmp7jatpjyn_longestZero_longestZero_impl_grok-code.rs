use vstd::prelude::*;

verus! {

spec fn get_size(i: int, j: int) -> int {
    j - i + 1
}

// For a given integer array, let's find the longest subsequence of 0s.
// sz: size, pos: position. a[pos..(pos+sz)] will be all zeros

// <vc-helpers>

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
    let mut max_len: usize = 0;
    let mut max_start: usize = 0;
    let mut curr_len: usize = 0;
    let mut curr_start: usize = 0;
    let mut idx: usize = 0;
    while idx < a.len()
        decreases (a.len() as int) - (idx as int)
        invariant
            0 <= idx <= a.len(),
            curr_start as int <= idx as int,
            curr_len as int <= idx as int - curr_start as int,
            max_len as int <= idx as int,
            max_start <= idx,
            forall |k: int| {
                (curr_start as int <= k < curr_start as int + curr_len as int) &&
                (curr_start as int + curr_len as int <= idx as int) ==> { a@[k] == 0 }
            },
            forall |p: int, q: int| {
                (0 <= p < q <= idx as int) &&
                (forall |k_inner: int| {
                    (p <= k_inner < q) ==> a@[k_inner] == 0
                }) ==> {
                    q - p <= max_len as int
                }
            }
    {
        if a[idx] == 0 {
            curr_len += 1;
            if curr_len > max_len {
                max_len = curr_len;
                max_start = curr_start;
            }
        } else {
            curr_len = 0;
            curr_start = idx + 1;
        }
        idx += 1;
    }
    proof {
        assert(forall |k: int| (max_start as int <= k < max_start as int + max_len as int) ==> a@[k] == 0);
        assert(max_len <= a.len());
        assert(max_start < a.len());
        assert(max_start + max_len <= a.len());
        assert(forall |i: int, j: int| (0 <= i < j < a.len() as int && j - i + 1 > max_len as int) ==>
               exists |k: int| (i <= k <= j && a@[k] != 0));
    }
    (max_len, max_start)
}
// </vc-code>

fn main() {}

}