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
/* helper modified by LLM (iteration 4): fixed decreases clause syntax and used correct Verus decreases format */
fn factorize_rec(number: i32, factor: i32, mut acc: Vec<i8>) -> Vec<i8>
    decreases number, factor
{
    if number == 1 {
        acc
    } else if factor * factor > number {
        if number > 1 {
            acc.push(number as i8);
        }
        acc
    } else if number % factor == 0 {
        acc.push(factor as i8);
        let new_number = number / factor;
        factorize_rec(new_number, factor, acc)
    } else {
        factorize_rec(number, factor + 1, acc)
    }
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
/* code modified by LLM (iteration 4): implement prime factorization calling the concrete recursive helper */
{
    if n <= 1 {
        Vec::new()
    } else {
        let number = n as i32;
        factorize_rec(number, 2, Vec::new())
    }
}
// </vc-code>


}

fn main() {}