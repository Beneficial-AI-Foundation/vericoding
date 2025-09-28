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
/* helper modified by LLM (iteration 5): Fixing nat/int usage in exec code by using ghost wrappers */
fn mod_pow(base: int, exp: int, modulus: int) -> (result: int)
    requires
        modulus > 0,
        exp >= 0,
    ensures
        result == pow(base, exp, modulus),
{
    if exp == 0 {
        1 % modulus
    } else {
        let half = mod_pow(base, exp / 2, modulus);
        let result_sq = (half * half) % modulus;
        if exp % 2 == 0 {
            result_sq
        } else {
            (result_sq * base) % modulus
        }
    }
}

/* helper modified by LLM (iteration 5): Converting to ghost function and using nat parameters */
ghost fn compute_block_count_ghost(n: int, i: int) -> (result: int)
    requires
        n >= 1,
        1 <= i <= n,
    ensures
        result == block_count_formula(n, i) % MOD,
{
    if i == n {
        10 % MOD
    } else {
        let exp1 = n - i - 1;
        let term1 = (2 * 9 * pow(10, exp1, MOD)) % MOD;
        let mut term2 = 0;
        if i < n - 1 {
            let exp2 = n - i - 2;
            term2 = (((n - 1 - i) * 9 * 9) % MOD * pow(10, exp2, MOD)) % MOD;
        }
        ((term1 + term2) % MOD * 10) % MOD
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<i8>)
  requires valid_input(n as int)
  ensures valid_result(result@.map(|_index: int, x: i8| x as int), n as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Using ghost function for computation and fixed type handling */
{
    let n_int = n as int;
    let mut result: Vec<i8> = Vec::new();
    
    proof {
        assert(valid_input(n_int));
    }
    
    let mut i: int = 1;
    while i <= n_int
        invariant
            i >= 1,
            i <= n_int + 1,
            result@.len() == (i - 1),
            forall|k: int| 0 <= k < result@.len() ==> #[trigger] result@[k] as int == compute_block_count_ghost(n_int, k + 1),
        decreases n_int - i
    {
        ghost {
            let val_int = compute_block_count_ghost(n_int, i);
            result.push(val_int as i8);
        }
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}