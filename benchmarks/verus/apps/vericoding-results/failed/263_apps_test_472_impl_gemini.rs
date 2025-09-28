// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn digit_sum(n: int) -> int
  decreases n when n >= 0
{
  if n <= 0 { 
    0 
  } else { 
    (n % 10) + digit_sum(n / 10) 
  }
}
// </vc-preamble>

// <vc-helpers>
fn compute_digit_sum(mut n: i8) -> (sum: i8)
    requires n >= 0
    ensures sum as int == digit_sum(n as int),
{
    let mut sum: i8 = 0;
    let mut temp_n = n;
    while temp_n > 0
        invariant
            n >= 0,
            temp_n >= 0,
            sum >= 0,
            digit_sum(n as int) == digit_sum(temp_n as int) + sum as int,
        decreases temp_n
    {
        let digit = temp_n % 10;
        proof {
            assert(digit_sum(temp_n as int) == (temp_n % 10) as int + digit_sum((temp_n / 10) as int));
        }
        sum = sum + digit;
        temp_n = temp_n / 10;
    }
    sum
}

/* helper modified by LLM (iteration 5): [fix proofs and add lemma for digit_sum bounds] */
proof fn lemma_digit_sum_is_positive(x: int)
    requires x > 0
    ensures digit_sum(x) > 0
    decreases x
{
    if x < 10 {
        assert(x > 0 && x < 10);
        assert(x / 10 == 0);
        assert(x % 10 == x);
        assert(digit_sum(0) == 0);
        assert(digit_sum(x) == x % 10 + digit_sum(x/10));
        assert(digit_sum(x) == x);
    } else {
        lemma_digit_sum_is_positive(x / 10);
        assert(digit_sum(x / 10) > 0);
        assert(x % 10 >= 0);
        assert(digit_sum(x) == x % 10 + digit_sum(x / 10));
        assert(digit_sum(x) > 0);
    }
}

proof fn lemma_no_solution_for_x_ge_11(n: i8)
    requires n >= 1
    ensures forall|x: int| x >= 11 ==> x * x + digit_sum(x) * x != (n as int)
{
    assert forall|x: int| x >= 11 implies x * x + digit_sum(x) * x != (n as int) by {
        lemma_digit_sum_is_positive(x);
        assert(digit_sum(x) >= 1);
        
        let val = x * x + digit_sum(x) * x;

        vstd::arithmetic::mul_mono(11, 11, x, x);
        assert(x * x >= 121);

        vstd::arithmetic::mul_mono(1, 11, digit_sum(x), x);
        assert(digit_sum(x) * x >= 11);

        assert(val >= 121 + 11);
        assert(val >= 132);
        assert(n as int <= 127);
        assert(val != n as int);
    }
}

proof fn lemma_digit_sum_for_small_x(x: int)
    requires 1 <= x <= 10
    ensures 1 <= digit_sum(x) <= 9
{
    if x < 10 {
        assert(digit_sum(x) == x);
    } else { // x == 10
        assert(digit_sum(10) == 1);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
  requires 
    n >= 1,
  ensures 
    n == 1 ==> result == -1,
    n > 1 && result > 0 ==> (result as int) * (result as int) + digit_sum(result as int) * (result as int) == n as int,
    n > 1 && result > 0 ==> forall|y: int| y > 0 && y < result as int ==> y * y + digit_sum(y) * y != n as int,
    n > 1 && result == -1 ==> forall|x: int| x > 0 ==> x * x + digit_sum(x) * x != n as int,
    result == -1 || result > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [add invariants and helper calls to fix precondition/overflow] */
    if n == 1 {
        return -1;
    }
    let mut x: i8 = 1;
    while x < 11
        invariant
            n > 1,
            x >= 1,
            x <= 11,
            forall|y: int| 1 <= y && y < (x as int) ==>
                y * y + digit_sum(y) * y != (n as int),
        decreases 11i8 - x
    {
        let ds = compute_digit_sum(x);
        proof {
            lemma_digit_sum_for_small_x(x as int);
            assert(ds as int == digit_sum(x as int));
            assert(1 <= ds <= 9);
        }
        let val = (x as i32) * (x as i32) + (ds as i32) * (x as i32);
        if val == n as i32 {
            return x;
        }
        x = x + 1;
    }

    proof {
        lemma_no_solution_for_x_ge_11(n);
    }

    return -1;
}

// </vc-code>


}

fn main() {}