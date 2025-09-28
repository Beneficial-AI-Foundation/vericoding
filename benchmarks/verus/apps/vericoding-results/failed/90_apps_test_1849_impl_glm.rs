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
fn mod_pow(base: i32, exp: i32, modulus: i32) -> (result: i32)
    requires modulus > 1
    ensures result == pow(base as int, exp as int, modulus as int) as i32
    decreases exp
{
    if exp == 0 {
        1
    } else if exp % 2 == 0 {
        let half = mod_pow(base, exp / 2, modulus);
        let temp = (half as i64) * (half as i64) % (modulus as i64);
        temp as i32
    } else {
        let half = mod_pow(base, exp / 2, modulus);
        let temp = (half as i64) * (half as i64) % (modulus as i64);
        let temp2 = (temp * (base as i64)) % (modulus as i64);
        temp2 as i32
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<i8>)
  requires valid_input(n as int)
  ensures valid_result(result@.map(|_index: int, x: i8| x as int), n as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed use of int in non-ghost code by using i32 and i64 */
{
    let n_i32 = n as i32;
    let mut result_vec: Vec<i8> = Vec::new();
    for i in 0..n-1 {
        let j_i32 = (i+1) as i32;
        let exponent1 = n_i32 - j_i32 - 1;
        let term1 = (2_i64 * 9_i64 * (mod_pow(10, exponent1, MOD as i32) as i64) * 10_i64) % (MOD as i64);
        let term2 = if j_i32 < n_i32 - 1 {
            let exponent2 = n_i32 - j_i32 - 2;
            let count = (n_i32 - 1 - j_i32) as i64;
            (count * 9_i64 * 9_i64 * (mod_pow(10, exponent2, MOD as i32) as i64) * 10_i64) % (MOD as i64)
        } else {
            0
        };
        let value = (term1 + term2) % (MOD as i64);
        let value_i8 = (value % 256) as i8;
        result_vec.push(value_i8);
    }
    result_vec.push(10);
    result_vec
}
// </vc-code>


}

fn main() {}