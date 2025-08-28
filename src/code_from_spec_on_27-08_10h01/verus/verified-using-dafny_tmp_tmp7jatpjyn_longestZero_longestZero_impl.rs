use vstd::prelude::*;

verus! {

spec fn get_size(i: int, j: int) -> int {
    j - i + 1
}

// For a given integer array, let's find the longest subsequence of 0s.
// sz: size, pos: position. a[pos..(pos+sz)] will be all zeros

// <vc-helpers>
spec fn all_zeros_in_range(a: Seq<i32>, start: int, len: int) -> bool {
    forall |i: int| start <= i < start + len ==> a[i] == 0
}

spec fn exists_nonzero_in_range(a: Seq<i32>, start: int, end: int) -> bool {
    exists |k: int| start <= k <= end && a[k] != 0
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    let mut max_len: usize = 0;
    let mut max_pos: usize = 0;
    let mut current_len: usize = 0;
    let mut current_pos: usize = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            max_len <= i,
            max_pos < a.len(),
            max_pos + max_len <= a.len(),
            current_pos <= i,
            current_pos < a.len() || (current_pos == 0 && i == 0),
            current_pos + current_len <= i,
            forall |k: int| max_pos <= k < (max_pos + max_len) ==> a@[k] == 0,
            forall |k: int| current_pos <= k < (current_pos + current_len) ==> a@[k] == 0,
            forall |start: int, end: int| {
                0 <= start <= end < i && get_size(start, end) > (max_len as int)
                ==> exists |k: int| start <= k <= end && a@[k] != 0
            },
            current_len == 0 ==> (i == 0 || (i > 0 && a@[(i-1) as int] != 0)),
            current_len > 0 ==> (current_pos + current_len == i && forall |k: int| current_pos <= k < i ==> a@[k] == 0),
        decreases a.len() - i
    {
        if a[i] == 0 {
            if current_len == 0 {
                current_pos = i;
                current_len = 1;
            } else {
                current_len = current_len + 1;
            }
        } else {
            proof {
                if current_len > max_len {
                    assert(forall |start: int, end: int| {
                        0 <= start <= end < i && get_size(start, end) > (current_len as int)
                        ==> exists |k: int| start <= k <= end && a@[k] != 0
                    });
                }
                assert(forall |start: int, end: int| {
                    0 <= start <= end <= i && get_size(start, end) > (max_len.max(current_len) as int)
                    ==> exists |k: int| start <= k <= end && a@[k] != 0
                });
            }
            if current_len > max_len {
                max_len = current_len;
                max_pos = current_pos;
            }
            current_len = 0;
        }
        i = i + 1;
    }
    
    if current_len > max_len {
        max_len = current_len;
        max_pos = current_pos;
    }
    
    if max_len == 0 {
        let mut j = 0;
        while j < a.len()
            invariant
                j <= a.len(),
                forall |k: int| 0 <= k < j ==> a@[k] != 0,
            decreases a.len() - j
        {
            if a[j] == 0 {
                return (1, j);
            }
            j = j + 1;
        }
        return (0, 0);
    }
    
    (max_len, max_pos)
}
// </vc-code>

fn main() {}

}