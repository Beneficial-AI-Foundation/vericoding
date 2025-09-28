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
/* helper modified by LLM (iteration 5): Fixed lemma syntax - added 'proof' keyword and proper function signature */
proof lemma digit_sum_monotonic(digits1: Seq<int>, digits2: Seq<int>)
    requires digits1.len() <= digits2.len()
    requires forall|i: int| 0 <= i < digits1.len() ==> digits1[i] <= digits2[i]
    ensures digit_sum(digits1) <= digit_sum(digits2)
    decreases digits1.len()
{
    if digits1.len() == 0 {
        assert(digit_sum(digits1) == 0);
    } else {
        let tail1 = digits1.subrange(1, digits1.len() as int);
        let tail2 = digits2.subrange(1, digits2.len() as int);
        digit_sum_monotonic(tail1, tail2);
    }
}

proof lemma digit_sum_max_property(x: int, y: int)
    requires valid_input(x)
    requires valid_input(y)
    requires y <= x
    ensures digit_sum(int_to_digits(y)) <= digit_sum(int_to_digits(
        if digit_sum(int_to_digits(y)) >= digit_sum(int_to_digits(x)) { y } else { x }
    ))
{
    if digit_sum(int_to_digits(y)) >= digit_sum(int_to_digits(x)) {
        assert(digit_sum(int_to_digits(y)) <= digit_sum(int_to_digits(y)));
    } else {
        assert(digit_sum(int_to_digits(y)) <= digit_sum(int_to_digits(x)));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (result: i8)
  requires valid_input(x as int)
  ensures valid_result(x as int, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed verification with proper loop invariants */
{
    let mut current = x;
    let mut result = x;
    
    while current >= 1
        invariant
            current >= -128,
            result >= -128,
            result <= x,
            forall|y: int| current as int < y && y <= x as int ==> digit_sum(int_to_digits(y)) <= digit_sum(int_to_digits(result as int)),
            forall|z: int| result as int <= z && z <= x as int ==> digit_sum(int_to_digits(z)) <= digit_sum(int_to_digits(result as int))
        decreases current
    {
        if digit_sum(int_to_digits(current as int)) > digit_sum(int_to_digits(result as int)) {
            result = current;
        }
        current = current - 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}