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
/* helper modified by LLM (iteration 5): fixed overflow by using int for total and casting at end */
fn digit_sum_exec(n: i8) -> (sum: i8)
    requires n >= 0
    ensures sum == digit_sum(int_to_digits(n as int)) as i8
{
    let mut num = n;
    let mut total: int = 0;
    while num > 0
        invariant
            num >= 0,
            total + digit_sum(int_to_digits(num as int)) == digit_sum(int_to_digits(n as int))
        decreases num as nat
    {
        total += (num % 10) as int;
        num = num / 10;
    }
    total as i8
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (result: i8)
  requires valid_input(x as int)
  ensures valid_result(x as int, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed invariant to use proper digit_sum function */
{
    let mut best_num: i8 = 1;
    let mut best_sum: int = digit_sum(int_to_digits(1));
    let mut candidate: int = 2;
    while candidate <= x as int
        invariant
            2 <= candidate,
            best_num >= 1,
            best_num as int < candidate,
            best_sum == digit_sum(int_to_digits(best_num as int)),
            forall|i: int| 1 <= i < candidate ==> digit_sum(int_to_digits(i)) <= best_sum,
            forall|i: int| 1 <= i < candidate && digit_sum(int_to_digits(i)) == best_sum ==> i <= best_num as int
        decreases (x as int) - candidate + 1
    {
        let sum_candidate_i8 = digit_sum_exec(candidate as i8);
        let sum_candidate: int = sum_candidate_i8 as int;
        if sum_candidate > best_sum {
            best_sum = sum_candidate;
            best_num = candidate as i8;
        } else if sum_candidate == best_sum {
            if candidate > best_num as int {
                best_num = candidate as i8;
            }
        }
        candidate += 1;
    }
    best_num
}
// </vc-code>


}

fn main() {}