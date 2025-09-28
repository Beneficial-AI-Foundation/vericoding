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
/* helper modified by LLM (iteration 5): simplified without overflow proofs */
fn exec_product_of_digits(x: i8) -> (result: i8)
    requires
        x >= 0,
        x <= 127
    ensures
        result as int == product_of_digits(x as int),
        result >= 1
{
    let mut num = x;
    let mut product = 1i8;
    
    if num == 0 {
        return 1;
    }
    
    while num > 0
        invariant
            num >= 0,
            product >= 1,
            product as int * product_of_digits(num as int) == product_of_digits(x as int)
        decreases num
    {
        let digit = num % 10;
        product = product * digit;
        num = num / 10;
    }
    
    product
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
    /* code modified by LLM (iteration 5): fixed invariant initialization and range bounds */
    let mut max_product = 1i8;
    let mut i = 1i8;
    
    proof {
        assert(max_product as int == max_product_of_digits_in_range(0));
    }
    
    while i <= n
        invariant
            1 <= i <= n + 1,
            max_product >= 1,
            max_product as int == max_product_of_digits_in_range((i - 1) as int)
        decreases (n + 1 - i) as nat
    {
        let current_product = exec_product_of_digits(i);
        if current_product > max_product {
            max_product = current_product;
        }
        i = i + 1;
    }
    
    max_product
}
// </vc-code>


}

fn main() {}