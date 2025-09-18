// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed parentheses from decreases clause to fix potential syntax error. */
fn compute_gcd_non_negative(a: i32, b: i32) -> (result: i32)
    requires a >= 0, b >= 0
    ensures
        result >= 0,
        result as int == gcd(a as int, b as int),
    decreases a as int + b as int
{
    if a == 0 && b == 0 {
        0
    } else if a == 0 {
        b
    } else if b == 0 {
        a
    } else if a >= b {
        compute_gcd_non_negative(b, a % b)
    } else {
        compute_gcd_non_negative(a, b % a)
    }
}

fn compute_gcd(a: i32, b: i32) -> (result: i32)
    ensures
        result >= 0,
        result as int == gcd(a as int, b as int),
{
    let abs_a = if a >= 0 { a } else { -a };
    let abs_b = if b >= 0 { b } else { -b };
    compute_gcd_non_negative(abs_a, abs_b)
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
    /* code modified by LLM (iteration 3): Added a decreases clause to the while loop to prove termination. */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] result[j] as int == gcd(x1[j] as int, x2[j] as int),
            forall|j: int| 0 <= j < i as int ==> result[j] >= 0,
        decreases x1.len() - i
    {
        let gcd_val = compute_gcd(x1[i], x2[i]);
        result.push(gcd_val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}