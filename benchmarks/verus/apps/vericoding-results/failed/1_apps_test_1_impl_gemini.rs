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
proof fn lemma_digit_sum_add(s1: Seq<int>, s2: Seq<int>)
    ensures digit_sum(s1.add(s2)) == digit_sum(s1) + digit_sum(s2)
    decreases s1.len()
{
    if s1.len() > 0 {
        assert(s1.add(s2).subrange(1, s1.add(s2).len() as int) == s1.subrange(1, s1.len() as int).add(s2));
        lemma_digit_sum_add(s1.subrange(1, s1.len() as int), s2);
    }
}

proof fn lemma_digit_sum_recursive(x: int)
    requires x >= 0
    ensures digit_sum(int_to_digits(x)) == if x < 10 { x } else { digit_sum(int_to_digits(x / 10)) + x % 10 }
{
    if x >= 10 {
        assert(x / 10 > 0);
        lemma_digit_sum_add(int_to_digits_helper(x / 10), seq![x % 10]);
    }
}

fn compute_digit_sum(n: i8) -> (sum: i8)
    requires
        n >= 0,
    ensures
        sum >= 0,
        sum as int == digit_sum(int_to_digits(n as int)),
{
    let mut temp_n = n;
    let mut sum: i8 = 0;
    while temp_n > 0
        invariant
            n >= 0,
            temp_n >= 0,
            sum >= 0,
            sum as int + digit_sum(int_to_digits(temp_n as int)) == digit_sum(int_to_digits(n as int)),
        decreases temp_n
    {
        proof {
            lemma_digit_sum_recursive(temp_n as int);
        }
        let digit = temp_n % 10;
        sum = sum + digit;
        temp_n = temp_n / 10;
    }
    sum
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (result: i8)
  requires valid_input(x as int)
  ensures valid_result(x as int, result as int)
// </vc-spec>
// <vc-code>
{
    // Handle the trivial case x=1, which simplifies the loop invariants.
    if x == 1 {
        return 1;
    }

    // Initialize the state with the solution for the range [1, 1].
    let mut result: i8 = 1;
    let mut max_digit_sum: i8 = compute_digit_sum(1);

    // Iterate from 2 up to x to find the number with the maximal digit sum.
    let mut i: i16 = 2; // Use i16 to prevent overflow on `i+1` when i=127
    while i <= (x as i16)
        invariant
            x >= 1,
            i >= 2,
            1 <= result <= x,
            max_digit_sum as int == digit_sum(int_to_digits(result as int)),
            forall|y: int| 1 <= y < i ==> digit_sum(int_to_digits(y)) <= max_digit_sum as int,
            forall|y: int| 1 <= y < i && digit_sum(int_to_digits(y)) == max_digit_sum as int ==> y <= result as int,
        decreases (x as i16) - i
    {
        let current_digit_sum = compute_digit_sum(i as i8);
        if current_digit_sum >= max_digit_sum {
            max_digit_sum = current_digit_sum;
            result = i as i8;
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}