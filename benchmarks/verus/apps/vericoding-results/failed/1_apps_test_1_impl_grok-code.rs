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
fn compute_digit_sum(x: i8) -> i8
    requires x >= 0
    ensures digit_sum(int_to_digits(x as int)) == result as int
    decreases x
{
    if x == 0 { 0 }
    else { compute_digit_sum(x / 10) + x % 10 }
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (result: i8)
  requires valid_input(x as int)
  ensures valid_result(x as int, result as int)
// </vc-spec>
// <vc-code>
{
    let mut y = 1i8;
    let mut best_y = 1i8;
    let mut best_sum = compute_digit_sum(1);
    while y < x
        invariant
            1 <= y <= x,
            1 <= best_y <= y,
            valid_input(x as int),
            best_sum as int == digit_sum(int_to_digits(best_y as int)),
            forall |z: int| 1 <= z <= y as int ==> digit_sum(int_to_digits(z)) >= best_sum as int,
            forall |z: int| 1 <= z <= y as int && digit_sum(int_to_digits(z)) == best_sum as int ==> z >= best_y as int,
        decreases (x - y) as int
    {
        y = y + 1;
        let current_sum = compute_digit_sum(y);
        if current_sum < best_sum {
            best_sum = current_sum;
            best_y = y;
        } else if current_sum == best_sum && y < best_y {
            best_y = y;
        }
    }
    best_y
}
// </vc-code>


}

fn main() {}