// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_boring_apartment(x: int) -> bool {
    (x >= 1 && x <= 9) ||
    (x >= 11 && x <= 99 && x % 11 == 0 && x / 11 >= 1 && x / 11 <= 9) ||
    (x >= 111 && x <= 999 && x % 111 == 0 && x / 111 >= 1 && x / 111 <= 9) ||
    (x >= 1111 && x <= 9999 && x % 1111 == 0 && x / 1111 >= 1 && x / 1111 <= 9)
}

spec fn digit_count(n: int) -> int {
    if n <= 9 { 1 }
    else if n <= 99 { 2 }
    else if n <= 999 { 3 }
    else { 4 }
}

spec fn boring_apartment_value(digit: int, length: int) -> int {
    if length == 1 { digit }
    else if length == 2 { digit * 11 }
    else if length == 3 { digit * 111 }
    else { digit * 1111 }
}

spec fn total_digits_pressed(x: int) -> int {
    let digit = if x <= 9 { x } 
                 else if x <= 99 { x / 11 }
                 else if x <= 999 { x / 111 }
                 else { x / 1111 };
    let length = digit_count(x);

    let prev_digits = if digit == 1 { 0 } else { (digit - 1) * (1 + 2 + 3 + 4) };

    let current_digits = (length * (length + 1)) / 2;

    prev_digits + current_digits
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(x: int) -> (result: int)
    requires is_boring_apartment(x) && 1 <= x <= 9999
    ensures result >= 0 && result == total_digits_pressed(x) && 
            (x == 1 ==> result == 1) &&
            (x == 22 ==> result == 13) &&
            (x == 777 ==> result == 66) &&
            (x == 9999 ==> result == 90)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}