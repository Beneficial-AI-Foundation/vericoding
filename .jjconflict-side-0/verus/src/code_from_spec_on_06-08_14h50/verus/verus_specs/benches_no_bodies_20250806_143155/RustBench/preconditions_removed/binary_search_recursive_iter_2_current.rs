use vstd::prelude::*;

verus! {

fn binary_search_recursive(v: &[i32], elem: i32, c: isize, f: isize) -> (p: isize)
    ensures
        -1 <= p < v.len(),
        forall|u: int| 0 <= u <= p ==> v[u] <= elem,
        forall|w: int| p < w < v.len() ==> v[w] > elem,
    decreases f - c + 1
{
    if c > f {
        // Search range is empty, find the rightmost valid position
        /* code modified by LLM (iteration 1): Fixed result type from usize to isize and added proper type conversions */
        let mut result: isize = -1;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                -1 <= result < v.len(),
                forall|u: int| 0 <= u <= result ==> v[u] <= elem,
                forall|u: int| result < u < i ==> v[u] > elem,
        {
            if v[i] <= elem {
                result = i as isize;
            }
            i += 1;
        }
        result
    } else {
        let mid = c + (f - c) / 2;
        /* code modified by LLM (iteration 1): Fixed type conversions for bounds checking and array indexing */
        if mid >= 0 && mid < v.len() as isize {
            if v[mid as usize] <= elem {
                binary_search_recursive(v, elem, mid + 1, f)
            } else {
                binary_search_recursive(v, elem, c, mid - 1)
            }
        } else {
            // mid is out of bounds, adjust the search range
            if mid < 0 {
                binary_search_recursive(v, elem, 0, f)
            } else {
                binary_search_recursive(v, elem, c, (v.len() - 1) as isize)
            }
        }
    }
}

fn main() {}
}