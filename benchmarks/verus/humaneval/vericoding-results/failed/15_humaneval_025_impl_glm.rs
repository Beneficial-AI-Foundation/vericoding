// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime(n: int) -> bool {
    n >= 2 && forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0
}

spec fn product(factors: Seq<int>) -> int
    decreases factors.len()
{
    if factors.len() == 0 {
        1
    } else {
        factors[0] * product(factors.subrange(1, factors.len() as int))
    }
}

spec fn is_non_decreasing(factors: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < factors.len() ==> #[trigger] factors[i] <= #[trigger] factors[j]
}

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added mod_op function for trigger in quantifier */
spec fn mod_op(a: int, b: int) -> int {
    a % b
}
// </vc-helpers>

// <vc-spec>
fn factorize(n: i8) -> (factors: Vec<i8>)
    requires n >= 0
    ensures 
        n <= 1 ==> factors.len() == 0,
        n > 1 ==> product(factors@.map(|i: int, x: i8| x as int)) == n as int,
        forall|i: int| 0 <= i < factors.len() ==> is_prime(#[trigger] factors@[i] as int),
        is_non_decreasing(factors@.map(|i: int, x: i8| x as int)),
        forall|i: int| 0 <= i < factors.len() ==> #[trigger] factors@[i] >= 2
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Replaced modulo operator with mod_op function call in trigger */
{
    if n <= 1 {
        return Vec::new();
    }
    let mut factors: Vec<i8> = Vec::new();
    let mut remaining: i8 = n;
    let mut d: i8 = 2;
    while d * d <= remaining
        invariant
            factors.len() >= 0,
            remaining as int >= 1,
            product(factors@.map(|i: int, x: i8| x as int)) * (remaining as int) == n as int,
            forall|i: int| 0 <= i < factors.len() ==> is_prime(factors@[i] as int),
            is_non_decreasing(factors@.map(|i: int, x: i8| x as int)),
            forall|i: int| 0 <= i < factors.len() ==> factors@[i] >= 2,
            d as int >= 2,
            forall|k: int| 2 <= k < (d as int) ==> #[trigger] mod_op(remaining as int, k) != 0
        decreases remaining as int
    {
        if remaining % d == 0 {
            factors.push(d);
            remaining = remaining / d;
        } else {
            d = d + 1;
        }
    }
    if remaining > 1 {
        factors.push(remaining);
    }
    factors
}
// </vc-code>


}

fn main() {}