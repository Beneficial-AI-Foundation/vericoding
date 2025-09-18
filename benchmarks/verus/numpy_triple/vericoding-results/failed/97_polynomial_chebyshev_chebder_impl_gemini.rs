// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn chebder(c: Vec<i32>, scl: i32) -> (result: Vec<i32>)
    requires c.len() > 0,
    ensures
        result.len() == c.len() - 1,
        c.len() > 1 ==> result[0] == scl * c[1],
        c.len() > 2 ==> result[1] == scl * 4 * c[2],
        forall|j: int| 2 <= j < result.len() ==>
            result[j] == scl * (2 * ((j + 1) as i32)) * c[j + 1],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by using Vec::from_elem instead of the non-existent Vec::new_with_len */
    let n = c.len();
    if n <= 1 {
        return Vec::new();
    }

    let mut result = Vec::from_elem(0i32, (n - 1) as usize);
    
    result.set(0, scl * c[1]);

    let mut j: usize = 1;
    while j < n - 1
        invariant
            n == c.len(),
            c.len() > 1,
            1 <= j && j <= n - 1,
            result.len() == (n - 1) as nat,
            result@[0] == scl * c@[1],
            forall|k: int| 1 <= k && k < j ==> 
                result@[k] == scl * (2 * ((k + 1) as i32)) * c@[k + 1],
        decreases n - 1 - j
    {
        let val = scl * (2 * ((j as i32) + 1)) * c[(j + 1) as usize];
        result.set(j, val);
        j = j + 1;
    }
    
    result
}

// </vc-code>

}
fn main() {}