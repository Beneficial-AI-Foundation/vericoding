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

proof fn lemma_digit_count_bounds(n: int)
    requires 1 <= n <= 9999
    ensures 1 <= digit_count(n) <= 4
{
}

proof fn lemma_boring_apartment_structure(x: int)
    requires is_boring_apartment(x)
    ensures 
        (digit_count(x) == 1 ==> x >= 1 && x <= 9),
        (digit_count(x) == 2 ==> x % 11 == 0 && x / 11 >= 1 && x / 11 <= 9),
        (digit_count(x) == 3 ==> x % 111 == 0 && x / 111 >= 1 && x / 111 <= 9),
        (digit_count(x) == 4 ==> x % 1111 == 0 && x / 1111 >= 1 && x / 1111 <= 9)
{
}

proof fn lemma_total_digits_correct(digit: int, length: int)
    requires 1 <= digit <= 9, 1 <= length <= 4
    ensures total_digits_pressed(boring_apartment_value(digit, length)) == 
            (digit - 1) * 10 + (length * (length + 1)) / 2
{
}

proof fn lemma_cast_safe(x: i32)
    requires is_boring_apartment(x as int) && 1 <= x as int <= 9999
    ensures x >= 1 && x <= 9999
{
}

// </vc-helpers>

// <vc-spec>
fn solve(x: i32) -> (result: i32)
    requires is_boring_apartment(x as int) && 1 <= x as int <= 9999
    ensures result as int >= 0 && result as int == total_digits_pressed(x as int) && 
            (x as int == 1 ==> result as int == 1) &&
            (x as int == 22 ==> result as int == 13) &&
            (x as int == 777 ==> result as int == 66) &&
            (x as int == 9999 ==> result as int == 90)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fix compilation error by removing direct int cast */
    proof { lemma_cast_safe(x); }
    
    let x_val: i32 = x;
    
    proof {
        let x_ghost = x_val as int;
        lemma_digit_count_bounds(x_ghost);
        lemma_boring_apartment_structure(x_ghost);
        
        let digit_ghost = if x_ghost <= 9 { x_ghost } 
                       else if x_ghost <= 99 { x_ghost / 11 }
                       else if x_ghost <= 999 { x_ghost / 111 }
                       else { x_ghost / 1111 };
        
        let length_ghost = if x_ghost <= 9 { 1 }
                        else if x_ghost <= 99 { 2 }
                        else if x_ghost <= 999 { 3 }
                        else { 4 };
        
        lemma_total_digits_correct(digit_ghost, length_ghost);
    }
    
    let digit_i32 = if x_val <= 9 { x_val } 
                  else if x_val <= 99 { x_val / 11 }
                  else if x_val <= 999 { x_val / 111 }
                  else { x_val / 1111 };
    
    let length_i32 = if x_val <= 9 { 1 }
                   else if x_val <= 99 { 2 }
                   else if x_val <= 999 { 3 }
                   else { 4 };
    
    let prev_digits = if digit_i32 == 1 { 0 } else { (digit_i32 - 1) * 10 };
    let current_digits = (length_i32 * (length_i32 + 1)) / 2;
    prev_digits + current_digits
}
// </vc-code>


}

fn main() {}