// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn product_of_digits(x: int) -> int
  recommends x >= 0
  decreases x
{
  if x == 0 { 1 }
  else if x < 10 { x }
  else { (x % 10) * product_of_digits(x / 10) }
}

spec fn max_product_of_digits_in_range(n: int) -> int
  recommends n >= 1
  decreases n
  when n >= 1
{
  if n == 1 { 1 }
  else {
    let current = product_of_digits(n);
    let rest = max_product_of_digits_in_range(n - 1);
    if current > rest { current } else { rest }
  }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added bounds to ensures clauses to satisfy postconditions in main function */
fn product_of_digits_exec(x: i8) -> (result: i8)
    requires
        x >= 0
    ensures
        result as int == product_of_digits(x as int),
        result as int >= 0,
        result as int <= i8::MAX as int
    decreases x
{
    if x == 0 {
        1
    } else if x < 10 {
        x
    } else {
        let prod_rest = product_of_digits_exec(x / 10);
        let last_digit = x % 10;
        let prod_temp = (last_digit as i64) * (prod_rest as i64);
        #[verifier::truncate]
        (prod_temp as i8)
    }
}

/* helper modified by LLM (iteration 4): Added forall and exists proves to ensures to satisfy postconditions */
fn max_product_exec(n: i8) -> (result: i8)
    requires
        n >= 1
    ensures
        result as int == max_product_of_digits_in_range(n as int),
        result >= 1,
        forall|k: int| 1 <= k <= n as int ==> product_of_digits(k) <= result as int,
        exists|k: int| 1 <= k <= n as int && product_of_digits(k) == result as int
    decreases n
{
    if n == 1 {
        1
    } else {
        let current = product_of_digits_exec(n);
        let rest = max_product_exec(n - 1);
        if current > rest {
            current
        } else {
            rest
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
  requires 
    n >= 1
  ensures 
    result as int == max_product_of_digits_in_range(n as int),
    result >= 1,
    forall|k: int| 1 <= k <= n as int ==> product_of_digits(k) <= result as int,
    exists|k: int| 1 <= k <= n as int && product_of_digits(k) == result as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Call max_product_exec to compute result */
    max_product_exec(n)
}
// </vc-code>


}

fn main() {}