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
/* helper modified by LLM (iteration 4): lemma for arithmetic sum used in prev computation */
proof fn lemma_sum_1_to_4()
    ensures
        1int + 2int + 3int + 4int == 10int,
{
    assert(1int + 2int + 3int + 4int == 10int);
}

/* helper modified by LLM (iteration 4): reveal digit_count to expose its definition */
proof fn lemma_digit_count_def(x: int)
    ensures
        digit_count(x) == if x <= 9int { 1int } else if x <= 99int { 2int } else if x <= 999int { 3int } else { 4int },
{
    reveal(digit_count);
}

/* helper modified by LLM (iteration 4): reveal total_digits_pressed to expose its definition */
proof fn lemma_total_digits_pressed_def(x: int)
    ensures
        total_digits_pressed(x) == {
            let digit = if x <= 9int { x }
                         else if x <= 99int { x / 11int }
                         else if x <= 999int { x / 111int }
                         else { x / 1111int };
            let length = digit_count(x);
            let prev_digits = if digit == 1int { 0int } else { (digit - 1int) * (1int + 2int + 3int + 4int) };
            let current_digits = (length * (length + 1int)) / 2int;
            prev_digits + current_digits
        },
{
    reveal(total_digits_pressed);
    reveal(digit_count);
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
    /* code modified by LLM (iteration 4): move all `int`-suffixed literals into proof blocks and connect implementation to spec */
    let len: i32 = if x <= 9 { 1 } else if x <= 99 { 2 } else if x <= 999 { 3 } else { 4 };
    let digit: i32 = if x <= 9 { x } else if x <= 99 { x / 11 } else if x <= 999 { x / 111 } else { x / 1111 };

    let prev: i32 = if digit == 1 { 0 } else { (digit - 1) * 10 };
    let curr: i32 = (len * (len + 1)) / 2;
    let result0: i32 = prev + curr;

    let ghost xi: int = x as int;
    let ghost leni: int = len as int;
    let ghost digiti: int = digit as int;

    proof {
        lemma_sum_1_to_4();
        lemma_digit_count_def(xi);
        lemma_total_digits_pressed_def(xi);

        // Relate len to digit_count(xi)
        if x <= 9 {
            assert(xi <= 9int);
            assert(digit_count(xi) == 1int);
            assert(leni == 1int);
        } else if x <= 99 {
            assert(9int < xi && xi <= 99int);
            assert(digit_count(xi) == 2int);
            assert(leni == 2int);
        } else if x <= 999 {
            assert(99int < xi && xi <= 999int);
            assert(digit_count(xi) == 3int);
            assert(leni == 3int);
        } else {
            assert(999int < xi);
            assert(digit_count(xi) == 4int);
            assert(leni == 4int);
        }
        assert(leni == digit_count(xi));

        // Relate digit computation
        assert(digiti == (if xi <= 9int { xi } else if xi <= 99int { xi / 11int } else if xi <= 999int { xi / 111int } else { xi / 1111int }));

        // Relate prev and curr to spec expressions
        assert(prev as int == if digiti == 1int { 0int } else { (digiti - 1int) * (1int + 2int + 3int + 4int) });
        assert(curr as int == (leni * (leni + 1int)) / 2int);

        // Conclude equality with total_digits_pressed
        assert(result0 as int == total_digits_pressed(xi));

        // Non-negativity (follows from structure of the computation)
        assert(result0 as int >= 0int);

        // Example cases required by ensures
        if xi == 1int { assert(result0 as int == 1int); }
        if xi == 22int { assert(result0 as int == 13int); }
        if xi == 777int { assert(result0 as int == 66int); }
        if xi == 9999int { assert(result0 as int == 90int); }
    }

    result0
}
// </vc-code>


}

fn main() {}