// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed trigger annotation for quantifier */
proof fn gcd_properties(a: int, b: int)
    ensures gcd(a, b) >= 0,
            gcd(a, b) == gcd(b, a),
            (a != 0 || b != 0) ==> gcd(a, b) > 0,
            gcd(a, b) == gcd(int_abs(a), int_abs(b)),
            a % gcd(a, b) == 0,
            b % gcd(a, b) == 0,
            forall|d: int| (d > 0 && a % d == 0 && b % d == 0) ==> #[trigger] gcd(a, b) % d == 0
{ }

fn compute_gcd(a: i32, b: i32) -> (result: i32)
    ensures result as int == gcd(a as int, b as int),
            result >= 0
{
    let mut x = if a >= 0 { a } else { -a };
    let mut y = if b >= 0 { b } else { -b };
    
    while y != 0
        invariant gcd(x as int, y as int) == gcd(a as int, b as int),
                  x >= 0,
                  y >= 0
        decreases y
    {
        let temp = y;
        y = x % y;
        x = temp;
    }
    x
}
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
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < x1.len()
        invariant i <= x1.len(),
                  result.len() == i,
                  forall|j: int| 0 <= j < i ==> result[j] as int == gcd(x1[j] as int, x2[j] as int),
                  forall|j: int| 0 <= j < i ==> result[j] >= 0
        decreases x1.len() - i
    {
        proof { gcd_properties(x1[i as int] as int, x2[i as int] as int); }
        let gcd_val = compute_gcd(x1[i], x2[i]);
        result.push(gcd_val);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}