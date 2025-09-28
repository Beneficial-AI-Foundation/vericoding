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
/* helper modified by LLM (iteration 4): The previous attempt to fix the compilation error was incorrect. The `lemma` keyword was completely removed, which causes it to be treated as a regular function and conflicts with the original global `spec fn product_of_digits`. The correct fix is to ensure the definition has `lemma fn`. The body of the lemma `product_of_digits_u8_is_int` uses `product_of_digits_u8`, which is a distinct `fn` not a `spec fn`. The lemma proves the equivalence between a `fn` and a `spec fn`. */

spec fn product_of_digits_u8(x: int) -> int
  recommends
    x >= 0
  decreases x
{
  if x == 0 { 1 }
  else if x < 10 { x }
  else { (x % 10) * product_of_digits_u8(x / 10) }
}

lemma fn product_of_digits_u8_is_int(x: int)
  requires x >= 0
  ensures product_of_digits_u8(x) == product_of_digits(x)
{
  if x == 0 {
  } else if x < 10 {
  } else {
    product_of_digits_u8_is_int(x / 10);
    proof {
      assert((x % 10) * product_of_digits_u8(x / 10) == (x % 10) * product_of_digits(x / 10));
      assert((x % 10) * product_of_digits(x / 10) == product_of_digits(x));
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
/* code modified by LLM (iteration 4): Simplified helper function call to `product_of_digits` instead of `product_of_digits_u8_is_int` and `product_of_digits_u8`. Removed the call to `product_of_digits_u8_is_int` within the loop, as `product_of_digits` is a `spec fn` and can be used directly for verification. Updated the invariant `exists` clause to correctly use `i` instead of `i-1` as upper bound. */
{
    let n_int = n as int;
    let mut max_prod: int = 1;
    let mut i: int = 1;

    while i <= n_int
        invariant
            1 <= i,
            i <= n_int + 1,
            max_prod >= 1,
            forall|k: int| 1 <= k < i ==> product_of_digits(k) <= max_prod,
            exists|k: int| 1 <= k < i && product_of_digits(k) == max_prod,
        decreases n_int - i
    {
        // product_of_digits_u8_is_int(i); // No longer needed as we directly use spec fn product_of_digits
        if product_of_digits(i) > max_prod {
            max_prod = product_of_digits(i);
        }
        i = i + 1;
    }
    max_prod as i8
}
// </vc-code>


}

fn main() {}