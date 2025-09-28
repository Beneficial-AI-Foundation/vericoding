use vstd::prelude::*;

verus! {

spec fn get_size(i: int, j: int) -> int {
    j - i + 1
}

// For a given integer array, let's find the longest subsequence of 0s.
// sz: size, pos: position. a[pos..(pos+sz)] will be all zeros

// <vc-helpers>
verus! {

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
    let mut i: usize = 0;
    let mut max_len: usize = 0;
    let mut max_start: usize = 0;

    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            max_len <= a.len(),
            max_start <= a.len(),
            max_len + max_start <= a.len(),
            forall |k: int| max_start <= k < (max_start + max_len as int) ==> a[k] == 0,
            forall |start: int, end: int|
                #![trigger get_size(start, end)] // Add trigger for quantified expression
                0 <= start < end < i && start < a.len() && end < a.len() && get_size(start, end) > max_len as int
                ==> exists |k: int| start <= k <= end && a[k] != 0
        decreases a.len() - i // Added decreases clause
    {
        if a[i] == 0 {
            let mut j: usize = i;
            while j < a.len() && a[j] == 0
                invariant
                    i <= j && j <= a.len(),
                    forall |k: int| i <= k < j ==> a[k] == 0,
                    0 <= i && i <= a.len(),
                    max_len <= a.len(),
                    max_start <= a.len(),
                    max_len + max_start <= a.len(),
                    forall |k: int| max_start <= k < (max_start + max_len as int) ==> a[k] == 0,
                    forall |start: int, end: int|
                        #![trigger get_size(start, end)] // Add trigger for quantified expression
                        0 <= start < end < i && start < a.len() && end < a.len() && get_size(start, end) > max_len as int
                        ==> exists |k: int| start <= k <= end && a[k] != 0
                decreases a.len() - j // Added decreases clause
            {
                j += 1;
            }
            let current_len: usize = j - i;
            if current_len > max_len {
                max_len = current_len;
                max_start = i;
            }
            i = j;
        } else {
            i += 1;
        }
    }
    (max_len, max_start)
}
// </vc-code>

fn main() {}

}