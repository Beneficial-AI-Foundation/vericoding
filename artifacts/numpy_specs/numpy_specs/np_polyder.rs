use vstd::prelude::*;

verus! {

// SPEC
fn polyder(poly: &[int], m: usize) -> (ret: Vec<int>)
    requires 
        m > 0,
        m <= poly.len(),
    ensures ret.len() == poly.len() - m,
{
    let mut result = Vec::new();
    let mut i = 0;
    let target_len = poly.len() - m;
    while i < target_len
        invariant 
            i <= target_len,
            target_len == poly.len() - m,
            result.len() == i,
        decreases target_len - i,
    {
        assert(i < poly.len());
        result.push(poly[i]);
        i += 1;
    }
    result
}

}

fn main() {}