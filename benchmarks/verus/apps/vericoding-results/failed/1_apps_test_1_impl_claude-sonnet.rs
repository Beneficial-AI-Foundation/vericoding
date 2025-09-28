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
fn compute_digit_sum(n: i8) -> (sum: i8)
    requires n >= 1
    ensures sum > 0
{
    let mut num = n;
    let mut sum = 0i8;
    while num > 0
        invariant
            num >= 0,
            sum >= 0,
            sum <= n * 9,
        decreases num
    {
        sum = sum + (num % 10);
        num = num / 10;
    }
    if sum == 0 { 1 } else { sum }
}

/* helper modified by LLM (iteration 5): added decreases clause */
proof fn lemma_digit_sum_positive(x: int)
    requires x >= 1
    ensures digit_sum(int_to_digits(x)) > 0
    decreases x
{
    if x < 10 {
        assert(int_to_digits(x) == seq![x]);
        assert(digit_sum(seq![x]) == x);
    } else {
        lemma_digit_sum_positive(x / 10);
    }
}

/* helper modified by LLM (iteration 5): added decreases clause */
proof fn lemma_result_exists(x: int)
    requires x >= 1
    ensures exists|r: int| 1 <= r <= x && valid_result(x, r)
    decreases x
{
    assert(1 <= x);
    assert(digit_sum(int_to_digits(1)) > 0) by {
        lemma_digit_sum_positive(1);
    };
    assert(valid_result(x, x));
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (result: i8)
  requires valid_input(x as int)
  ensures valid_result(x as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed arithmetic overflow and invariants */
    let mut best = 1i8;
    let mut best_sum = compute_digit_sum(1);
    
    let mut i = 2i8;
    while i <= x
        invariant
            2 <= i <= x + 1,
            1 <= best <= x,
            best_sum > 0,
            best < i,
        decreases (x as int) - (i as int)
    {
        let current_sum = compute_digit_sum(i);
        if current_sum > best_sum || (current_sum == best_sum && i > best) {
            best = i;
            best_sum = current_sum;
        }
        i = (i + 1) as i8;
    }
    
    proof {
        lemma_digit_sum_positive(best as int);
        lemma_result_exists(x as int);
    }
    
    best
}
// </vc-code>


}

fn main() {}