// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn floor_div(a: i32, b: i32) -> (q: i32)
    requires
        b != 0,
    ensures
        a == q * b + (a - q * b),
        if b > 0 {
            0 <= (a - q * b) <= b - 1
        } else {
            b + 1 <= (a - q * b) <= 0
        },
{
    if b > 0 && a % b == 0 {
        let q = a / b;
        q
    } else if b < 0 && a % b == 0 {
        let q = a / b;
        q
    } else if b > 0 {
        let q = a / b;
        if a % b != 0 && a < 0 {
            q - 1
        } else {
            q
        }
    } else {
        let q = a / b;
        if a % b != 0 && a > 0 {
            q - 1
        } else {
            q
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn numpy_mod(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] != 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i] == x1[i] % x2[i],
        forall|i: int| 0 <= i < result.len() ==> {
            let r = #[trigger] result[i];
            let a = x1[i];
            let b = x2[i];
            /* Basic remainder property: a = floor_div(a, b) * b + r */
            a == (a / b) * b + r &&
            /* Result has same sign as divisor (when divisor is non-zero) */
            (b > 0 ==> r >= 0 && r < b) &&
            (b < 0 ==> r <= 0 && r > b)
        }
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i8> = Vec::new();
    for i in 0..x1.len() {
        let a: i32 = x1[i] as i32;
        let b: i32 = x2[i] as i32;
        let q = floor_div(a, b);
        let r: i32 = a - q * b;
        result.push(r as i8);
    }
    result
}
// </vc-code>


}
fn main() {}