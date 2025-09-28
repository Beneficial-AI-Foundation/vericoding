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
proof fn lemma_product_of_digits_nonnegative(x: int)
    requires
        x >= 0
    ensures
        product_of_digits(x) >= 1
    decreases x
{
    if x == 0 {
    } else if x < 10 {
    } else {
        lemma_product_of_digits_nonnegative(x / 10);
    }
}

proof fn lemma_max_product_monotonic(n: int, m: int)
    requires
        n >= 1,
        m >= 1,
        n <= m
    ensures
        max_product_of_digits_in_range(n) <= max_product_of_digits_in_range(m)
    decreases m
{
    if m > n {
        lemma_max_product_monotonic(n, m - 1);
        let current = product_of_digits(m);
        let rest = max_product_of_digits_in_range(m - 1);
    }
}

proof fn lemma_product_of_digits_ghost_valid(x: i8) -> (ghost_val: int)
    requires
        x >= 1
    ensures
        ghost_val == product_of_digits(x as int)
    decreases x as int
{
    if x < 10 {
        ghost_val = x as int;
    } else {
        let digit = x % 10;
        let remaining = x / 10;
        lemma_product_of_digits_ghost_valid(remaining);
        ghost_val = digit as int * ghost_val;
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
    /* code modified by LLM (iteration 5): Fixed compilation errors by using ghost function for spec computations */
    let mut max_product: i8 = 1;
    let mut current: i8 = n;
    
    while current >= 1
        invariant
            current >= 1,
            max_product as int == max_product_of_digits_in_range(current as int),
            forall|k: int| 1 <= k <= current as int ==> product_of_digits(k) <= max_product as int,
            exists|k: int| 1 <= k <= current as int && product_of_digits(k) == max_product as int
        decreases current
    {
        let x = current;
        proof {
            lemma_product_of_digits_nonnegative(x as int);
        }
        let prod_val = proof {
            lemma_product_of_digits_ghost_valid(x)
        };
        
        if prod_val > max_product as int {
            max_product = prod_val as i8;
        }
        
        current = current - 1;
    }
    
    max_product
}
// </vc-code>


}

fn main() {}