// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed gcd_lemma to use proper decreases clause syntax */
proof fn gcd_lemma(a: int, b: int) 
    ensures 
        gcd(a, b) == gcd(int_abs(a), int_abs(b)),
        gcd(a, b) == gcd(b, a),
        a != 0 || b != 0 ==> gcd(a, b) > 0,
        gcd(a, b) % a == 0 && gcd(a, b) % b == 0,
        forall|d: int| d % a == 0 && d % b == 0 ==> d % gcd(a, b) == 0
    decreases int_abs(a) + int_abs(b)
{
    if a == 0 && b == 0 {
        assert(gcd(0, 0) == 0);
        assert(0 % 0 == 0);
    } else if a == 0 {
        assert(gcd(0, b) == int_abs(b));
        assert(int_abs(b) % b == 0);
        assert(forall|d: int| d % 0 == 0 && d % b == 0 ==> d % int_abs(b) == 0);
    } else if b == 0 {
        assert(gcd(a, 0) == int_abs(a));
        assert(int_abs(a) % a == 0);
        assert(forall|d: int| d % a == 0 && d % 0 == 0 ==> d % int_abs(a) == 0);
    } else if int_abs(a) >= int_abs(b) {
        gcd_lemma(int_abs(b), int_abs(a) % int_abs(b));
    } else {
        gcd_lemma(int_abs(a), int_abs(b) % int_abs(a));
    }
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
/* code modified by LLM (iteration 5): Fixed invariant syntax with proper curly braces */
{
    let mut result: Vec<i32> = Vec::with_capacity(x1.len());
    let mut i: usize = 0;
    while i < x1.len()
        decreases x1.len() - i
        invariant {
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == gcd(x1[j] as int, x2[j] as int),
            forall|j: int| 0 <= j < i ==> result[j] >= 0,
            forall|j: int| 0 <= j < i ==> gcd(x1[j] as int, x2[j] as int) == gcd(int_abs(x1[j] as int), int_abs(x2[j] as int)),
            forall|j: int| 0 <= j < i ==> (x1[j] == 0 && x2[j] == 0) ==> result[j] == 0,
            forall|j: int| 0 <= j < i ==> (x1[j] != 0 && x2[j] == 0) ==> result[j] as int == int_abs(x1[j] as int),
            forall|j: int| 0 <= j < i ==> (x1[j] == 0 && x2[j] != 0) ==> result[j] as int == int_abs(x2[j] as int),
            forall|j: int| 0 <= j < i ==> (result[j] as int) % (x1[j] as int) == 0 && (result[j] as int) % (x2[j] as int) == 0,
            forall|j: int, d: int| 0 <= j < i ==> (d % (x1[j] as int) == 0 && d % (x2[j] as int) == 0) ==> d % (result[j] as int) == 0,
            forall|j: int| 0 <= j < i ==> gcd(x2[j] as int, x1[j] as int) == gcd(x1[j] as int, x2[j] as int)
        }
    {
        let a_val = x1[i];
        let b_val = x2[i];
        proof { 
            let a = a_val as int;
            let b = b_val as int;
            gcd_lemma(a, b); 
        }
        
        let gcd_val = if a_val == 0 && b_val == 0 {
            0
        } else if a_val == 0 {
            let abs_b = if b_val >= 0 { b_val } else { -b_val };
            abs_b
        } else if b_val == 0 {
            let abs_a = if a_val >= 0 { a_val } else { -a_val };
            abs_a
        } else {
            let mut x = if a_val >= 0 { a_val } else { -a_val } as u32;
            let mut y = if b_val >= 0 { b_val } else { -b_val } as u32;
            while y != 0
                invariant {
                    gcd(x as int, y as int) == gcd(a_val as int, b_val as int),
                    x > 0,
                    y >= 0
                }
                decreases y
            {
                let temp = y;
                y = x % y;
                x = temp;
            }
            x as i32
        };
        
        result.push(gcd_val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}