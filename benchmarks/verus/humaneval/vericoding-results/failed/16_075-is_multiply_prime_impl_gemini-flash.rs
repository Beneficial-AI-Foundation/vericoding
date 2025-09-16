// <vc-preamble>
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed as_int conversion from `abs_int` helper since `i` is already `int` type. Renamed `abs_int` to `abs`. */
spec fn abs(i: int) -> int { if i < 0 { -i } else { i } }
// </vc-helpers>

// <vc-spec>
fn is_multiply_prime(x: u32) -> (ans: bool)

    requires
        x > 1,

    ensures
        ans <==> exists|a: int, b: int, c: int|
            spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The `as int` casts were removed where int type was not necessary in `while` loop conditions, so now the conditions correctly use the `u32` variables as `u32` for `*` operator on `u32`. `i` is `u32`, so `i * i * i` is `u32`. This resolves the `The Verus types 'nat' and 'int' can only be used in ghost code` errors. */
{
    let ghost x_int = x as int;

    let mut i: u32 = 2;
    while (i * i) <= (x / i)
        invariant
            2 <= i,
            (i as int) <= x_int,
            // We only care about positive integers for primes, so no need for negative checks
            forall|a: int, b: int, c: int|
                #![trigger spec_prime(a), spec_prime(b), spec_prime(c)]
                (spec_prime(a) && spec_prime(b) && spec_prime(c) && x_int == a * b * c)
                ==>
                (abs(a) >= i as int || abs(b) >= i as int || abs(c) >= i as int),

        decreases x_int - (i as int)
    {
        if x % i == 0 {
            let ghost p1 = i as int;
            if spec_prime(p1) {
                let x_div_i = x / i;
                let mut j: u32 = i;
                while (j * j) <= x_div_i
                    invariant
                        2 <= i,
                        i <= j,
                        (j as int) <= x_div_i as int,
                        forall|a: int, b: int, c: int|
                            #![trigger spec_prime(a), spec_prime(b), spec_prime(c)]
                            (spec_prime(a) && spec_prime(b) && spec_prime(c) && x_int == a * b * c)
                            ==>
                            (abs(a) >= i as int || abs(b) >= j as int || abs(c) >= j as int),

                    decreases x_div_i - (j as int)
                {
                    if x_div_i % j == 0 {
                        let ghost p2 = j as int;
                        if spec_prime(p2) {
                            let p3_u32 = x_div_i / j;
                            let ghost p3 = p3_u32 as int;
                            if spec_prime(p3) {
                                // Found three prime factors
                                return true;
                            }
                        }
                    }
                    j = j + 1;
                }
            }
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}