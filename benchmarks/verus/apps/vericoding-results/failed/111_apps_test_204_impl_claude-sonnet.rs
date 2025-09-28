// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, x: int, y: int) -> bool {
  a > 0 && b > 0 && x > 0 && y > 0
}

spec fn gcd(a: int, b: int) -> int
  recommends a >= 0 && b >= 0
  decreases b when b >= 0
{
  if b == 0 { a } else { gcd(b, a % b) }
}

spec fn min(a: int, b: int) -> int {
  if a <= b { a } else { b }
}

spec fn expected_result(a: int, b: int, x: int, y: int) -> int
  recommends valid_input(a, b, x, y)
{
  let g = gcd(x, y);
  let x_reduced = x / g;
  let y_reduced = y / g;
  min(a / x_reduced, b / y_reduced)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix lemma syntax */
fn gcd_impl(mut a: i8, mut b: i8) -> (result: i8)
    requires
        a > 0,
        b >= 0,
    ensures
        result > 0,
        result as int == gcd(a as int, b as int),
        a % result == 0,
        b % result == 0,
    decreases b
{
    if b == 0 {
        a
    } else {
        gcd_impl(b, a % b)
    }
}

fn min_impl(a: i8, b: i8) -> (result: i8)
    requires
        a > 0,
        b > 0,
    ensures
        result > 0,
        result as int == min(a as int, b as int),
{
    if a <= b { a } else { b }
}

proof fn lemma_gcd_divides(a: int, b: int)
    requires
        a > 0,
        b >= 0,
    ensures
        a % gcd(a, b) == 0,
        b % gcd(a, b) == 0,
    decreases b
{
    if b == 0 {
        // base case: gcd(a, 0) = a, so a % a = 0
    } else {
        lemma_gcd_divides(b, a % b);
        // inductive case follows from recursive property
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, x: i8, y: i8) -> (result: i8)
requires 
  valid_input(a as int, b as int, x as int, y as int)
ensures 
  result as int >= 0,
  result as int == expected_result(a as int, b as int, x as int, y as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use gcd divisibility lemma */
    let g = gcd_impl(x, y);
    proof {
        lemma_gcd_divides(x as int, y as int);
        assert(x % g == 0);
        assert(y % g == 0);
    }
    let x_reduced = x / g;
    let y_reduced = y / g;
    proof {
        assert(x_reduced > 0);
        assert(y_reduced > 0);
        assert(a / x_reduced > 0);
        assert(b / y_reduced > 0);
    }
    let result = min_impl(a / x_reduced, b / y_reduced);
    result
}
// </vc-code>


}

fn main() {}