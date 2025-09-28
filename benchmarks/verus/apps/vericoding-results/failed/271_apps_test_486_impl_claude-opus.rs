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
/* helper modified by LLM (iteration 5): Added lemma for max product step property */
proof fn lemma_max_product_base()
    ensures
        max_product_of_digits_in_range(1) == 1,
        product_of_digits(1) == 1,
        product_of_digits(0) == 1,
{
    assert(product_of_digits(0) == 1);
    assert(product_of_digits(1) == 1);
    assert(max_product_of_digits_in_range(1) == 1);
}

/* helper modified by LLM (iteration 5): Added lemma for product properties */
proof fn lemma_product_properties(x: int)
    requires x >= 0
    ensures
        product_of_digits(x) >= 0,
        x == 0 ==> product_of_digits(x) == 1,
        0 < x < 10 ==> product_of_digits(x) == x,
    decreases x
{
    if x == 0 {
        assert(product_of_digits(0) == 1);
    } else if x < 10 {
        assert(product_of_digits(x) == x);
    } else {
        lemma_product_properties(x / 10);
    }
}

/* helper modified by LLM (iteration 5): Added lemma for max product step */
proof fn lemma_max_product_step(n: int)
    requires n >= 2
    ensures
        max_product_of_digits_in_range(n) == if product_of_digits(n) > max_product_of_digits_in_range(n - 1) {
            product_of_digits(n)
        } else {
            max_product_of_digits_in_range(n - 1)
        },
{
    // Direct from definition
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
/* code modified by LLM (iteration 5): Fixed invariants and overflow handling */
{
    proof {
        lemma_max_product_base();
    }
    
    let mut max = 1i8;
    let mut i = 1i8;
    
    while i <= n
        invariant
            1 <= i,
            i <= n + 1,
            max >= 1,
            max <= 127,
            forall|k: int| 1 <= k && k < i ==> product_of_digits(k) <= max as int,
            max as int == max_product_of_digits_in_range((i - 1) as int),
            exists|k: int| 1 <= k && k < i && product_of_digits(k) == max as int,
        decreases n - i + 1
    {
        let mut prod = 1i8;
        let mut temp = i;
        
        if temp < 10 {
            prod = temp;
            proof {
                assert(prod as int == product_of_digits(i as int));
            }
        } else {
            let orig_i = i;
            while temp > 0
                invariant
                    0 <= temp,
                    temp <= orig_i,
                    orig_i == i,
                    prod >= 0,
                    prod <= 127,
                    if temp == 0 {
                        prod as int == product_of_digits(orig_i as int)
                    } else if prod == 0 {
                        product_of_digits(orig_i as int) == 0
                    } else {
                        prod as int * product_of_digits(temp as int) == product_of_digits(orig_i as int)
                    },
                decreases temp
            {
                let digit = temp % 10;
                if digit == 0 {
                    prod = 0;
                } else if prod == 0 {
                    // prod stays 0
                } else {
                    // Check for overflow before multiplication
                    if prod <= 12 && digit <= 10 && prod * digit <= 127 {
                        prod = prod * digit;
                    } else {
                        // Cap at maximum value to avoid overflow
                        prod = 127;
                    }
                }
                temp = temp / 10;
            }
            proof {
                assert(prod as int == product_of_digits(i as int));
            }
        }
        
        proof {
            assert(prod as int == product_of_digits(i as int));
            if i >= 2 {
                lemma_max_product_step(i as int);
            }
        }
        
        if prod > max {
            max = prod;
        }
        
        proof {
            // After updating max, establish the invariant for next iteration
            assert(max as int == if product_of_digits(i as int) > max_product_of_digits_in_range((i - 1) as int) {
                product_of_digits(i as int)
            } else {
                max_product_of_digits_in_range((i - 1) as int)
            });
            assert(max as int == max_product_of_digits_in_range(i as int));
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == n + 1);
        assert(max as int == max_product_of_digits_in_range(n as int));
        assert(forall|k: int| 1 <= k <= n as int ==> product_of_digits(k) <= max as int);
        assert(exists|k: int| 1 <= k <= n as int && product_of_digits(k) == max as int);
    }
    
    max
}
// </vc-code>


}

fn main() {}