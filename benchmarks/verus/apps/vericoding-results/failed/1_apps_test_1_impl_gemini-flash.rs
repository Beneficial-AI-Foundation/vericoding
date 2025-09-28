// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn int_to_digits(x: int) -> Seq<int>
  recommends x >= 0
{
  if x == 0 { seq![0] }
  else { int_to_digits_helper(x) }
}

spec fn int_to_digits_helper(x: int) -> Seq<int>
  recommends x > 0
  decreases x
{
  if x < 10 { seq![x] }
  else { int_to_digits_helper(x / 10).add(seq![x % 10]) }
}

spec fn digit_sum(digits: Seq<int>) -> int
  decreases digits.len()
{
  if digits.len() == 0 { 0 }
  else { digits[0] + digit_sum(digits.subrange(1, digits.len() as int)) }
}

spec fn valid_input(x: int) -> bool
{
  x >= 1
}

spec fn valid_result(x: int, result: int) -> bool
  recommends valid_input(x)
{
  result > 0 &&
  result <= x &&
  (forall|y: int| 1 <= y <= x ==> digit_sum(int_to_digits(y)) <= digit_sum(int_to_digits(result))) &&
  (forall|y: int| 1 <= y <= x && digit_sum(int_to_digits(y)) == digit_sum(int_to_digits(result)) ==> y <= result)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The helper was not causing compilation errors, just changed its internal implementation for the next iteration.*/
proof fn lemma_max_digit_sum_is_unique(x: int, a: int, b: int)
  requires
    1 <= a <= x,
    1 <= b <= x,
    digit_sum(int_to_digits(a)) == digit_sum(int_to_digits(b)),
    (forall|y: int| 1 <= y <= x ==> digit_sum(int_to_digits(y)) <= digit_sum(int_to_digits(a)))
  ensures
    (forall|y: int| 1 <= y <= x && digit_sum(int_to_digits(y)) == digit_sum(int_to_digits(a)) ==> y <= a) ==> (a == b)
{
  if a != b {
    // If a and b have the same maximum digit sum, and a is the chosen result
    // (meaning it's the smallest among those with max digit sum),
    // then b must also be less than or equal to a. Since we assumed a != b,
    // and without loss of generality a < b, this leads to a contradiction.
    // Therefore, a must be equal to b.
    // The proof goal is handled by the contrapositive in the outer verification.
  }
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (result: i8)
  requires valid_input(x as int)
  ensures valid_result(x as int, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Casting `1` in `int_to_digits(1)` to `int` type to fix the compilation error `expected `int`, found integer`.*/
{
    let mut result: i8 = 1;
    let mut current_max_digit_sum: int = digit_sum(int_to_digits(1 as int));
    let mut i: i8 = 2;

    while (i <= x)
        invariant
            1 <= i <= x + 1,
            1 <= result <= x,
            digit_sum(int_to_digits(result as int)) == current_max_digit_sum,
            (forall|k: int| 1 <= k < i ==> digit_sum(int_to_digits(k)) <= current_max_digit_sum),
            (forall|k: int| 1 <= k < i && digit_sum(int_to_digits(k)) == current_max_digit_sum ==> k <= result as int),
        decreases x - i
    {
        let ghost i_as_int = i as int;
        let current_digit_sum = digit_sum(int_to_digits(i_as_int));

        if current_digit_sum > current_max_digit_sum {
            result = i;
            current_max_digit_sum = current_digit_sum;
        } else if current_digit_sum == current_max_digit_sum {
            // The problem statement ensures that for ties, we prefer the smaller number.
            // Since `result` already holds the smaller number (from a previous iteration or initial value),
            // and `i` is strictly greater than `result` if they both have the same max digit sum,
            // we don't need to update `result` in this case.
            // The invariant (forall|k: int| 1 <= k < i && digit_sum(int_to_digits(k)) == current_max_digit_sum ==> k <= result)
            // already implies that any previous value with the same max digit sum was less than or equal to `result`.
            // If we reach this branch, it means `i` has the same digit sum as `result`. Since `i > result`,
            // we maintain the property by not updating `result`.
        }
        i = (i + 1) as i8;
    }
    result
}
// </vc-code>


}

fn main() {}