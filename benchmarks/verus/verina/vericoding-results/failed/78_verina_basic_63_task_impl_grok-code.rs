// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn has_close_elements(numbers: &Vec<i32>, threshold: i32) -> (result: bool)
    requires threshold >= 0,
    ensures
        !result <==> (forall|i: int, j: int| 
            0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j ==> 
            abs_diff(numbers[i] as int, numbers[j] as int) >= threshold as int),
// </vc-spec>
// <vc-code>
{
    let n = numbers.len();
    let mut i = 0;
    #[invariant forall |p:int, q:int| !(0 <= p < i && p < q < n) || abs_diff(numbers@[p as int] as int, numbers@[q as int] as int) >= threshold as int]
    while i < n {
        let mut j = i + 1;
        #[invariant forall |r:int| !(i+1 <= r < j) || abs_diff(numbers@[i as int] as int, numbers@[r as int] as int) >= threshold as int]
        while j < n {
            if abs_diff(numbers@[i as int] as int, numbers@[j as int] as int) < threshold as int {
                return true;
            }
            j += 1;
        }
        i += 1;
    }
    false
}
// </vc-code>

}
fn main() {}