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
fn count_digits(n: i8) -> (result: i8)
    requires
        n >= 1,
    ensures
        result >= 1,
        result as int == num_digits(n as int),
{
    let mut num = n;
    let mut count = 0i8;
    while num > 0
        invariant
            count >= 0,
            num >= 0,
            count as int + num_digits(num as int) == num_digits(n as int),
    {
        num = num / 10;
        count = count + 1;
    }
    count
}

lemma lemma_factor_pair_symmetric(a: int, b: int, n: int)
    requires
        is_factor_pair(a, b, n),
    ensures
        is_factor_pair(b, a, n),
{}

lemma lemma_f_symmetric(a: int, b: int)
    requires
        a >= 1,
        b >= 1,
    ensures
        f(a, b) == f(b, a),
{}
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
{
    let mut min_f = i8::MAX;
    let mut i = 1i8;
    
    while i <= n
        invariant
            i >= 1,
            i <= n + 1,
            min_f >= 1,
            exists|a: int, b: int| is_factor_pair(a, b, n as int) && min_f as int == f(a, b),
            forall|a: int, b: int| #[trigger] is_factor_pair(a, b, n as int) && a < i ==> min_f as int <= f(a, b),
    {
        if n % i == 0 {
            let j = n / i;
            let digits_i = count_digits(i);
            let digits_j = count_digits(j);
            let current_f = if digits_i > digits_j { digits_i } else { digits_j };
            
            if current_f < min_f {
                min_f = current_f;
            }
        }
        i = i + 1;
    }
    
    min_f
}
// </vc-code>


}

fn main() {}