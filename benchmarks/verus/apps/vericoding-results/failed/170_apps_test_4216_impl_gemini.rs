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
fn num_digits_exec(n: i8) -> (result: i8)
    requires
        n >= 1,
    ensures
        result as int == num_digits(n as int),
        result >= 1,
    decreases n
{
    if n < 10 {
        1
    } else {
        1 + num_digits_exec(n / 10)
    }
}

fn f_exec(a: i8, b: i8) -> (result: i8)
    requires
        a >= 1,
        b >= 1,
    ensures
        result as int == f(a as int, b as int),
        result >= 1,
{
    let digits_a = num_digits_exec(a);
    let digits_b = num_digits_exec(b);
    if digits_a > digits_b {
        digits_a
    } else {
        digits_b
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
    let n_int = n as int;

    let mut min_res = f_exec(1, n);
    let mut witness_a: int = 1;
    let mut witness_b: int = n_int;

    let mut i: i8 = 1;
    while i <= n
        invariant
            1 <= i <= n + 1,
            n_int == n as int,
            is_factor_pair(witness_a, witness_b, n_int),
            min_res as int == f(witness_a, witness_b),
            forall|a: int, b: int|
                (is_factor_pair(a, b, n_int) && a < i as int)
                ==> min_res as int <= f(a, b),
        decreases n - i
    {
        if n % i == 0 {
            let a = i;
            let b = n / i;
            assert(is_factor_pair(a as int, b as int, n_int));

            let current_f = f_exec(a, b);
            assert(current_f as int == f(a as int, b as int));

            if current_f < min_res {
                min_res = current_f;
                witness_a = a as int;
                witness_b = b as int;
            }
        }
        i = i + 1;
    }

    min_res
}
// </vc-code>


}

fn main() {}