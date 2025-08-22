use vstd::prelude::*;

verus! {

fn binary_search_recursive(v: &[i32], elem: i32, c: isize, f: isize) -> (p: isize)
    ensures
        -1 <= p < v@.len(),
        forall|u: int| 0 <= u <= p ==> v@[u] <= elem,
        forall|w: int| p < w < v@.len() ==> v@[w] > elem,
    decreases f - c + 1
{
    if c > f {
        return -1;
    }
    
    let mid = c + (f - c) / 2;
    
    /* code modified by LLM (iteration 1): fixed compilation error by converting nat to int for comparison */
    if 0 <= mid && mid < v@.len() as int {
        if v[mid as usize] <= elem {
            if mid == f || (mid + 1 < v@.len() as int && v[(mid + 1) as usize] > elem) {
                return mid;
            } else {
                return binary_search_recursive(v, elem, mid + 1, f);
            }
        } else {
            return binary_search_recursive(v, elem, c, mid - 1);
        }
    } else {
        return binary_search_recursive(v, elem, c, mid - 1);
    }
}

fn main() {}
}