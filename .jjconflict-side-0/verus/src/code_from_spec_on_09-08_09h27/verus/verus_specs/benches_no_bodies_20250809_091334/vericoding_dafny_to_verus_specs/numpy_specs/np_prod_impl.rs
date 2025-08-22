use vstd::prelude::*;

verus! {

// Specification function to compute product of array elements from start to end
spec fn prod_array(a: &[int], start: int, end: int) -> int
    recommends
        0 <= start <= end <= a.len(),
    decreases
        end - start,
{
    if start >= end {
        1
    } else {
        a[start] * prod_array(a, start + 1, end)
    }
}

}

fn main() {}