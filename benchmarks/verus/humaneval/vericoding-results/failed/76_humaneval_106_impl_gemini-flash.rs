// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n <= 1 { 1 } else { n * factorial((n - 1) as nat) }
}

spec fn sum_range(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { n + sum_range((n - 1) as nat) }
}

spec fn valid_result(n: nat, result: Seq<nat>) -> bool
{
    result.len() == n &&
    forall|i: int| 0 <= i < n ==> 
        (if (i + 1) % 2 == 0 { result[i] == factorial((i + 1) as nat) }
         else { result[i] == sum_range((i + 1) as nat) })
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn f(n: u8) -> (result: Vec<u8>)
    ensures valid_result(n as nat, result@.map(|i: int, x: u8| x as nat))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Corrected type casting from `nat` to `u8` for `current_val_nat` declaration */
    let mut result: Vec<u8> = Vec::new();
    let mut i: u8 = 0;

    while i < n
        invariant
            result.len() == i as nat,
            forall|j: int| 0 <= j < i as int ==> (
                if (j + 1) % 2 == 0 { result@[j] == factorial((j + 1) as nat) as u8 }
                else { result@[j] == sum_range((j + 1) as nat) as u8 }
            ),
            i <= n,
        decreases (n - i) as int
    {
        let val_to_add: u8;
        let current_val_nat_val: nat = (i as nat) + 1; // Renamed to avoid reserved keyword
        if current_val_nat_val % 2 == 0 {
            val_to_add = factorial(current_val_nat_val) as u8;
        } else {
            val_to_add = sum_range(current_val_nat_val) as u8;
        }
        result.push(val_to_add);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}