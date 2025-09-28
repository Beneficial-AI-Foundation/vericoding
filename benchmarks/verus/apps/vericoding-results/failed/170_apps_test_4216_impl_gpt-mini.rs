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
/* helper modified by LLM (iteration 5): runtime digits function bridging to spec num_digits */
fn digits_i64(n: i64) -> i64
    requires n >= 1,
    ensures result as int == num_digits(n as int),
    decreases n
{
    if n < 10 { 1 } else { 1 + digits_i64(n / 10) }
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
/* code modified by LLM (iteration 5): iterate factors, track minimal digit-width factor pair using digits_i64 helper and prove postconditions */
{
    let n_i64: i64 = n as i64;
    let mut best_a: i64 = 1;
    let mut best_b: i64 = n_i64;
    let mut best: i64 = digits_i64(n_i64);
    let mut i: i64 = 2;
    while i <= n_i64
        invariant
            best >= 1,
            best_a >= 1,
            best_b >= 1,
            best_a * best_b == n_i64,
            best == (if digits_i64(best_a) > digits_i64(best_b) { digits_i64(best_a) } else { digits_i64(best_b) }),
            best <= digits_i64(n_i64),
            forall|a: i64, b: i64| ((a >= 1 && b >= 1 && a * b == n_i64) && a < i) ==> best <= (if digits_i64(a) > digits_i64(b) { digits_i64(a) } else { digits_i64(b) }),
        decreases n_i64 - i + 1
    {
        if n_i64 % i == 0 {
            let j: i64 = n_i64 / i;
            let da: i64 = digits_i64(i);
            let db: i64 = digits_i64(j);
            let cand: i64 = if da > db { da } else { db };
            if cand < best {
                best = cand;
                best_a = i;
                best_b = j;
            }
        }
        i = i + 1;
    }
    let result: i8 = best as i8;
    proof {
        let n_spec: int = n_i64 as int;
        assert(best_a >= 1 && best_b >= 1 && best_a * best_b == n_i64);
        assert((best_a as int) * (best_b as int) == n_spec);
        assert(is_factor_pair(best_a as int, best_b as int, n_spec));
        assert(best as int == f(best_a as int, best_b as int));
        assert(result as int == f(best_a as int, best_b as int));
        assert(exists|a: int, b: int| is_factor_pair(a, b, n_spec) && result as int == f(a, b));
        assert(forall|a: int, b: int| is_factor_pair(a, b, n_spec) ==> result as int <= f(a, b));
    }
    result
}
// </vc-code>


}

fn main() {}