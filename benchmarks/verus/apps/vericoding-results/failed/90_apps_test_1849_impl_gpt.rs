// <vc-preamble>
use vstd::prelude::*;

verus! {

spec const MOD: int = 998244353int;

spec fn valid_input(n: int) -> bool
{
  n >= 1
}

spec fn pow(base: int, exp: int, modulus: int) -> int
  decreases exp
{
  if exp <= 0 { 1int }
  else { (base * pow(base, exp - 1, modulus)) % modulus }
}

spec fn block_count_formula(n: int, i: int) -> int
  recommends n >= 1 && 1 <= i <= n
{
  if i == n { 10int }
  else { 
    ((2int * 9int * pow(10int, n - i - 1, MOD) * 10int) + 
     (if i < n - 1 { ((n - 1 - i) * 9int * 9int * pow(10int, n - i - 2, MOD) * 10int) } else { 0int })) % MOD
  }
}

spec fn valid_result(result: Seq<int>, n: int) -> bool
  recommends n >= 1
{
  result.len() == n &&
  (forall|k: int| 0 <= k < n ==> #[trigger] result[k] >= 0 && #[trigger] result[k] < MOD) &&
  (n >= 1 ==> result[n-1] == 10int) &&
  (forall|i: int| 0 <= i < n-1 ==> #[trigger] result[i] == block_count_formula(n, i+1))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): executable helper to compute modular exponentiation with a proper decreases clause */
fn pow_mod_exec(base: i128, exp: i128, modulus: i128) -> i128 {
    let mut result: i128 = ((1i128 % modulus) + modulus) % modulus;
    let mut b = ((base % modulus) + modulus) % modulus;
    let mut e = exp;
    while e > 0
        invariant
            e >= 0,
        decreases e as int
    {
        result = (result * b) % modulus;
        e = e - 1;
    }
    result
}

/* helper modified by LLM (iteration 5): executable helper to compute block_count_formula */
fn block_count_formula_exec(n: i128, i: i128, modulus: i128) -> i128 {
    if i == n { 10 } else {
        let term1 = (2i128 * 9i128 % modulus) * pow_mod_exec(10, n - i - 1, modulus) % modulus * 10 % modulus;
        let term2 = if i < n - 1 {
            ((n - 1 - i) % modulus + modulus) % modulus * 9i128 % modulus * 9i128 % modulus * pow_mod_exec(10, n - i - 2, modulus) % modulus * 10 % modulus
        } else { 0 };
        (term1 + term2) % modulus
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<i8>)
  requires valid_input(n as int)
  ensures valid_result(result@.map(|_index: int, x: i8| x as int), n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): add loop decreases clause and compute using exec helpers */
    let ni: i128 = n as i128;
    let mut result: Vec<i8> = Vec::new();
    let mut i: i128 = 1;
    let modulus: i128 = 998244353i128;
    while i <= ni
        invariant
            i >= 1,
        decreases (ni - i) as int
    {
        let val: i128 = block_count_formula_exec(ni, i, modulus);
        let x: i8 = val as i8;
        result.push(x);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}