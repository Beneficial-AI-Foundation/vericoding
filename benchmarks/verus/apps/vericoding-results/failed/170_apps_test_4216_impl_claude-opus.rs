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
proof fn num_digits_positive(n: int)
    requires
        n >= 1,
    ensures
        num_digits(n) >= 1,
    decreases n
{
    if n < 10 {
        assert(num_digits(n) == 1);
    } else {
        num_digits_positive(n / 10);
        assert(num_digits(n) == 1 + num_digits(n / 10));
    }
}

proof fn factor_pair_exists(n: int)
    requires
        n >= 1,
    ensures
        exists|a: int, b: int| is_factor_pair(a, b, n),
{
    assert(is_factor_pair(1, n, n));
}

/* helper modified by LLM (iteration 5): Fixed count upper bound for i8 max value */
fn compute_num_digits(n: i8) -> (result: i8)
    requires
        n >= 1,
        n <= 127,
    ensures
        result >= 1,
        result as int == num_digits(n as int),
{
    let mut temp = n;
    let mut count: i8 = 0;
    
    while temp > 0
        invariant
            0 <= temp <= 127,
            0 <= count <= 127,
            n >= 1,
            if temp == 0 {
                count as int == num_digits(n as int)
            } else {
                count as int + num_digits(temp as int) == num_digits(n as int)
            },
        decreases temp
    {
        count = count + 1;
        temp = temp / 10;
    }
    
    proof {
        num_digits_positive(n as int);
    }
    
    count
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
{
    /* code modified by LLM (iteration 5): Fixed b validation and loop termination */
    let digits_n = compute_num_digits(n);
    let mut max_f: i8 = digits_n;
    let mut a: i8 = 1;
    
    proof {
        factor_pair_exists(n as int);
        assert(is_factor_pair(1, n as int, n as int));
        assert(f(1, n as int) == if num_digits(1) > num_digits(n as int) { num_digits(1) } else { num_digits(n as int) });
        assert(num_digits(1) == 1);
        num_digits_positive(n as int);
        assert(f(1, n as int) == num_digits(n as int));
        assert(max_f as int == f(1, n as int));
    }
    
    while a <= n
        invariant
            1 <= a <= n + 1,
            max_f >= 1,
            exists|x: int, y: int| is_factor_pair(x, y, n as int) && max_f as int == f(x, y),
            forall|x: int, y: int| is_factor_pair(x, y, n as int) && x < a as int ==> max_f as int >= f(x, y),
        decreases n - a + 1
    {
        if n % a == 0 {
            let b = n / a;
            assert(b >= 1) by {
                assert(a >= 1);
                assert(n >= 1);
                assert(a * b == n);
            }
            let digits_a = compute_num_digits(a);
            let digits_b = compute_num_digits(b);
            let current_f = if digits_a > digits_b { digits_a } else { digits_b };
            
            proof {
                assert(a as int * b as int == n as int) by {
                    assert(n % a == 0);
                    assert(b == n / a);
                }
                assert(is_factor_pair(a as int, b as int, n as int));
                assert(f(a as int, b as int) == current_f as int);
            }
            
            if current_f > max_f {
                max_f = current_f;
                proof {
                    assert(is_factor_pair(a as int, b as int, n as int));
                    assert(max_f as int == f(a as int, b as int));
                }
            }
        }
        a = a + 1;
    }
    
    proof {
        assert(a > n);
        assert(forall|x: int, y: int| is_factor_pair(x, y, n as int) ==> max_f as int >= f(x, y)) by {
            assert(forall|x: int, y: int| is_factor_pair(x, y, n as int) && x <= n as int ==> max_f as int >= f(x, y));
            assert(forall|x: int, y: int| is_factor_pair(x, y, n as int) && x > n as int ==> false);
        }
    }
    
    max_f
}
// </vc-code>


}

fn main() {}