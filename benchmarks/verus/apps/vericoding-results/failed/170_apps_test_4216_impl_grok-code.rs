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
/* helper modified by LLM (iteration 4): Changed all int types to i32 in executable functions for compilation, added casts for specs where needed */
fn exec_num_digits(n: i32) -> i32
    requires
        n >= 1,
{
    let mut count: i32 = 0;
    let mut x: i32 = n;
    while x > 0
        invariant
            count >= 0,
            x >= 0,
        decreases x + 1
    {
        count += 1;
        x /= 10;
    }
    count
}

spec fn is_minimum(max_vals: Vec<i32>, m: i32) -> bool
  recommends max_vals.len() >= 1 && forall|i: int| 0 <= i < max_vals.len() ==> max_vals@[i] >= 1,
  decreases max_vals.len()
{
    forall|i: int| 0 <= i < max_vals.len() ==> max_vals@[i] >= m
}

fn compute_max_digits(a: i32, b: i32) -> i32
    requires
        a >= 1,
        b >= 1,
{
    let da = exec_num_digits(a);
    let db = exec_num_digits(b);
    if da > db {
        da
    } else {
        db
    }
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
    /* code modified by LLM (iteration 5): Fixed assert by syntax with missing parentheses */
    let mut max_vals: Vec<i32> = Vec::new();
    let nn: i32 = n as i32;
    let mut i: i32 = 1;
    while i <= nn
        invariant
            forall|j: int| 0 <= j < max_vals.len() ==> max_vals@[j] >= 1,
            max_vals.len() >= 0,
        decreases
            (nn as int) - (i as int) + 1
    {
        if nn % i == 0 {
            let b = nn / i;
            let mx = compute_max_digits(i, b);
            max_vals.push(mx);
        }
        i += 1;
    }
    proof {
        assert(max_vals.len() > 0) by(nonlinear_arith);
    }
    let mut min_val: i32 = max_vals@[0];
    let len = max_vals.len();
    let mut k: usize = 0;
    while k < len
        invariant
            0 <= k <= len,
            min_val <= max_vals@[0],
            forall|j: int| 0 <= j < k ==> max_vals@[j] >= min_val,
        decreases
            len - k
    {
        let current = max_vals@[k];
        if current < min_val {
            min_val = current;
        }
        k += 1;
    }
    let result = min_val as i8;
    proof {
        assert(is_minimum(max_vals, min_val));
        assert(exists|a: int, b: int| is_factor_pair(a, b, nn as int) && (min_val as int) == f(a, b));
        assert(forall|a: int, b: int| is_factor_pair(a, b, nn as int) ==> f(a, b) >= min_val);
    }
    result
}
// </vc-code>


}

fn main() {}