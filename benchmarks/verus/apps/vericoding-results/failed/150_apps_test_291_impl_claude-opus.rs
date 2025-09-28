// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn pow(base: int, exp: int) -> int
  decreases exp
{
  if exp <= 0 { 1 }
  else { base * pow(base, exp - 1) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added stronger overflow bounds and recursive call proof */
fn compute_pow(base: i32, exp: i8) -> (result: i32)
    requires
        exp >= 0,
        base >= 0,
        exp <= 20,
        base <= 10,
        pow(base as int, exp as int) <= i32::MAX,
    ensures
        result == pow(base as int, exp as int),
    decreases exp,
{
    if exp == 0 {
        proof {
            assert(pow(base as int, 0) == 1);
        }
        1
    } else {
        proof {
            assert(exp - 1 >= 0);
            assert(exp - 1 <= 20);
            assert(pow(base as int, (exp - 1) as int) <= pow(base as int, exp as int));
            assert(pow(base as int, (exp - 1) as int) <= i32::MAX);
        }
        let sub_result = compute_pow(base, (exp - 1) as i8);
        proof {
            assert(sub_result == pow(base as int, (exp - 1) as int));
            assert(pow(base as int, exp as int) == base * pow(base as int, (exp - 1) as int));
            assert(base * sub_result == pow(base as int, exp as int));
            assert(base * sub_result <= i32::MAX);
        }
        base * sub_result
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (years: i8)
  requires 
      1 <= a <= b <= 10,
      forall|base: int, exp: int| exp >= 0 ==> (
          (exp == 0 ==> pow(base, exp) == 1) &&
          (exp > 0 && base > 0 ==> pow(base, exp) > 0) &&
          (exp > 0 && base == 0 ==> pow(base, exp) == 0)
      ),
  ensures 
      years >= 0,
      (a as int) * pow(3, years as int) > (b as int) * pow(2, years as int),
      years == 0 || (a as int) * pow(3, (years - 1) as int) <= (b as int) * pow(2, (years - 1) as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added overflow bounds and fixed loop exit logic */
    let mut y: i8 = 0;
    let mut a_power: i32 = a as i32;
    let mut b_power: i32 = b as i32;
    
    while a_power <= b_power && y < 20
        invariant
            0 <= y <= 20,
            a_power == (a as int) * pow(3, y as int),
            b_power == (b as int) * pow(2, y as int),
            y == 0 || (a as int) * pow(3, (y - 1) as int) <= (b as int) * pow(2, (y - 1) as int),
            1 <= a <= b <= 10,
            a_power >= 0,
            b_power >= 0,
            a_power <= 10 * pow(3, 20),
            b_power <= 10 * pow(2, 20),
            pow(3, (y + 1) as int) <= pow(3, 20),
            pow(2, (y + 1) as int) <= pow(2, 20),
            a_power * 3 <= i32::MAX,
            b_power * 2 <= i32::MAX,
        decreases 20 - y,
    {
        let old_a_power = a_power;
        let old_b_power = b_power;
        
        y = y + 1;
        
        proof {
            assert(a_power * 3 <= 10 * pow(3, y as int));
            assert(10 * pow(3, y as int) <= 10 * pow(3, 20));
            assert(10 * pow(3, 20) <= i32::MAX);
        }
        a_power = a_power * 3;
        
        proof {
            assert(b_power * 2 <= 10 * pow(2, y as int));
            assert(10 * pow(2, y as int) <= 10 * pow(2, 20));
            assert(10 * pow(2, 20) <= i32::MAX);
        }
        b_power = b_power * 2;
        
        proof {
            assert(pow(3, y as int) == 3 * pow(3, (y - 1) as int));
            assert(pow(2, y as int) == 2 * pow(2, (y - 1) as int));
            assert(old_a_power == (a as int) * pow(3, (y - 1) as int));
            assert(old_b_power == (b as int) * pow(2, (y - 1) as int));
            assert(a_power == old_a_power * 3);
            assert(b_power == old_b_power * 2);
            assert(a_power == (a as int) * pow(3, y as int));
            assert(b_power == (b as int) * pow(2, y as int));
        }
    }
    
    proof {
        assert(a_power > b_power || y == 20);
        if y < 20 {
            assert(a_power > b_power);
            assert((a as int) * pow(3, y as int) > (b as int) * pow(2, y as int));
        } else {
            assert(y == 20);
            assert(a >= 1);
            assert(b <= 10);
            assert(pow(3, 20) > 10 * pow(2, 20));
            assert((a as int) * pow(3, 20) >= pow(3, 20));
            assert((b as int) * pow(2, 20) <= 10 * pow(2, 20));
            assert((a as int) * pow(3, 20) > (b as int) * pow(2, 20));
        }
    }
    
    y
}
// </vc-code>


}

fn main() {}