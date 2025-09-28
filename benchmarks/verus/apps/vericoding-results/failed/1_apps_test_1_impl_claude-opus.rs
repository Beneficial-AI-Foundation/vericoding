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
/* helper modified by LLM (iteration 3): Added decreases clause to recursive proof function */
proof fn digits_sum_positive(n: int)
    requires n >= 1
    ensures digit_sum(int_to_digits(n)) >= 1
    decreases n
{
    if n < 10 {
        assert(int_to_digits(n) == seq![n]);
        assert(digit_sum(seq![n]) == n);
    } else {
        digits_sum_positive(n / 10);
        assert(n % 10 >= 0);
    }
}

proof fn digit_sum_bounded(n: int)
    requires n >= 1
    ensures digit_sum(int_to_digits(n)) <= n * 9
    decreases n
{
    if n < 10 {
        assert(int_to_digits(n) == seq![n]);
        assert(digit_sum(seq![n]) == n);
        assert(n <= 9);
    } else {
        digit_sum_bounded(n / 10);
        let digits = int_to_digits(n);
        let prefix = int_to_digits(n / 10);
        assert(digits == prefix.add(seq![n % 10]));
        assert(n % 10 <= 9);
    }
}

fn compute_digit_sum(n: i8) -> (sum: i8)
    requires n >= 0
    ensures sum as int == digit_sum(int_to_digits(n as int))
{
    let mut result: i8 = 0;
    let mut temp = n;
    
    while temp > 0
        invariant
            0 <= temp <= n,
            result >= 0,
            result as int + digit_sum(int_to_digits(temp as int)) == digit_sum(int_to_digits(n as int)),
        decreases temp
    {
        let digit = temp % 10;
        result = result + digit;
        temp = temp / 10;
        
        proof {
            if temp == 0 {
                assert(int_to_digits(0) == seq![0int]);
                assert(digit_sum(seq![0int]) == 0);
            }
        }
    }
    
    if n == 0 {
        result = 0;
        proof {
            assert(int_to_digits(0) == seq![0int]);
            assert(digit_sum(seq![0int]) == 0);
        }
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (result: i8)
  requires valid_input(x as int)
  ensures valid_result(x as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): No changes needed in main code */
    let mut best_result: i8 = 1;
    let mut best_sum: i8 = compute_digit_sum(1);
    let mut i: i8 = 1;
    
    proof {
        digits_sum_positive(1);
        assert(digit_sum(int_to_digits(1)) == 1);
    }
    
    while i <= x
        invariant
            1 <= i <= x + 1,
            1 <= best_result < i,
            best_result <= x,
            best_sum as int == digit_sum(int_to_digits(best_result as int)),
            best_sum >= 1,
            forall|y: int| 1 <= y < i ==> digit_sum(int_to_digits(y)) <= digit_sum(int_to_digits(best_result as int)),
            forall|y: int| 1 <= y < i && digit_sum(int_to_digits(y)) == digit_sum(int_to_digits(best_result as int)) ==> y <= best_result as int,
        decreases x - i + 1
    {
        let current_sum = compute_digit_sum(i);
        
        proof {
            digits_sum_positive(i as int);
        }
        
        if current_sum >= best_sum {
            best_sum = current_sum;
            best_result = i;
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == x + 1);
        assert(forall|y: int| 1 <= y <= x ==> digit_sum(int_to_digits(y)) <= digit_sum(int_to_digits(best_result as int)));
        assert(forall|y: int| 1 <= y <= x && digit_sum(int_to_digits(y)) == digit_sum(int_to_digits(best_result as int)) ==> y <= best_result as int);
        digits_sum_positive(best_result as int);
    }
    
    best_result
}
// </vc-code>


}

fn main() {}