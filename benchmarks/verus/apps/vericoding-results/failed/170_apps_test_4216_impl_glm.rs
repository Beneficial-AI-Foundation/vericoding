// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn num_digits(n: int) -> int
  recommends n >= 1
  decreases n
{
  if n < 10 { 1 } else { 1 + num_digits(n / 10) }
}

spec fn valid_input(n: int) -> bool {
  n >= 1
}

spec fn f(a: int, b: int) -> int
  recommends a >= 1 && b >= 1
{
  let digits_a = num_digits(a);
  let digits_b = num_digits(b);
  if digits_a > digits_b { digits_a } else { digits_b }
}

spec fn is_factor_pair(a: int, b: int, n: int) -> bool {
  a >= 1 && b >= 1 && a * b == n
}
// </vc-preamble>

// <vc-helpers>
fn exec_digits_i8(x: i8) -> (d: i8)
    requires 1 <= x <= 127
    ensures d == num_digits(x as int)
{
    if x < 10 {
        1
    } else if x < 100 {
        2
    } else {
        3
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
  requires 
    valid_input(n as int)
  ensures 
    result >= 1,
    exists|a: int, b: int| is_factor_pair(a, b, n as int) && result as int == f(a, b),
    forall|a: int, b: int| is_factor_pair(a, b, n as int) ==> result as int <= f(a, b),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added trigger for quantifier in invariant */
{
    let mut min_d = 3 as i8;
    let mut a: u8 = 1;

    while a <= n as u8
        invariant
            1 <= a as int <= (n as int) + 1,
            min_d >= 1,
            a as int > 1 ==> min_d <= 3,
            forall|a_prime: int| 1 <= a_prime < a as int && (n as int) % a_prime == 0 ==> min_d <= #[trigger] f(a_prime, (n as int) / a_prime),
            a as int > 1 ==> exists|a0: int| 1 <= a0 < a as int && (n as int) % a0 == 0 && min_d == f(a0, (n as int) / a0),
        decreases (n as int) - (a as int)
    {
        let a_i8 = a as i8;
        if n % a_i8 == 0 {
            let b = n / a_i8;
            let d_a = exec_digits_i8(a_i8);
            let d_b = exec_digits_i8(b);
            let d = if d_a > d_b { d_a } else { d_b };
            if d < min_d {
                min_d = d;
            }
        }
        a = a + 1;
    }
    min_d
}
// </vc-code>


}

fn main() {}