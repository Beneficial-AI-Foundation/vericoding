// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn gcd(a: int, b: int) -> int 
decreases int_abs(a) + int_abs(b), 

{
    if a == 0 && b == 0 {
        0
    } else if a == 0 {
        int_abs(b)
    } else if b == 0 {
        int_abs(a)
    } else if int_abs(a) >= int_abs(b) {
        gcd(int_abs(b), int_abs(a) % int_abs(b))
    } else {
        gcd(int_abs(a), int_abs(b) % int_abs(a))
    }
}


spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

fn numpy_gcd(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == gcd(#[trigger] x1[i] as int, #[trigger]  x2[i] as int),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < result.len() ==> gcd(#[trigger] x1[i] as int, x2[i] as int) == gcd(#[trigger] int_abs(x1[i] as int), #[trigger] int_abs(x2[i] as int)),
        forall|i: int| 0 <= i < result.len() ==> (x1[i] == 0 && x2[i] == 0) ==> #[trigger] result[i] == 0,
        forall|i: int| 0 <= i < result.len() ==> (x1[i] != 0 && x2[i] == 0) ==> #[trigger] result[i] as int == int_abs(x1[i] as int),
        forall|i: int| 0 <= i < result.len() ==> (x1[i] == 0 && x2[i] != 0) ==> #[trigger] result[i] as int == int_abs(x2[i] as int),
        forall|i: int| 0 <= i < result.len() ==> (result[i] as int) % (x1[i] as int) == 0 && (result[i] as int) % (x2[i] as int) == 0,
        forall|i: int, d: int| 0 <= i < result.len() 
            ==>  (d % (x1[i] as int) == 0 && d % (x2[i] as int) == 0) ==> #[trigger] (d % (result[i] as int)) == 0,
        forall|i: int| 0 <= i < result.len() ==> gcd(x2[i] as int, #[trigger] x1[i] as int) == gcd(x1[i] as int, #[trigger] x2[i] as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): removed duplicate int_abs helper and kept implementation */
{
    let n = x1.len();
    let mut result_vec: Vec<i32> = Vec::with_capacity(n);
    result_vec.set_len(n);
    
    for i in 0..n
        invariant
            result_vec.len() == n,
            forall|j: int| 0 <= j < i ==> result_vec[j] as int == gcd(x1[j] as int, x2[j] as int),
            forall|j: int| 0 <= j < i ==> result_vec[j] >= 0,
    {
        let a = x1[i];
        let b = x2[i];
        
        let mut x = if a >= 0 { a } else { -a };
        let mut y = if b >= 0 { b } else { -b };
        
        while y != 0
            invariant
                gcd(x as int, y as int) == gcd(a as int, b as int),
                x >= 0,
                y >= 0,
                decreases y,
        {
            let temp = y;
            y = x % y;
            x = temp;
        }
        
        if x == 0 && y == 0 {
            result_vec[i] = 0;
        } else {
            result_vec[i] = x;
        }
    }
    
    result_vec
}
// </vc-code>

}
fn main() {}