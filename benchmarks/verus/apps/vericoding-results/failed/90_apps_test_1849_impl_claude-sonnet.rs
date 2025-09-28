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
/* helper modified by LLM (iteration 5): fixed overflow by using explicit casts and bounds checks */
fn mod_pow(base: i64, exp: i64, modulus: i64) -> (result: i64)
    requires
        modulus > 0,
        exp >= 0,
        base >= 0,
        base < modulus,
    ensures
        result == pow(base as int, exp as int, modulus as int),
        result >= 0,
        result < modulus,
    decreases exp
{
    if exp == 0 {
        1
    } else if exp == 1 {
        base
    } else {
        let prev = mod_pow(base, exp - 1, modulus);
        ((base as u64 * prev as u64) % modulus as u64) as i64
    }
}

/* helper modified by LLM (iteration 5): fixed overflow with u64 arithmetic and proper casting */
fn compute_block_count(n: i8, i: i8) -> (result: i64)
    requires
        n >= 1,
        1 <= i <= n,
        n <= 30,
    ensures
        result == block_count_formula(n as int, i as int),
        result >= 0,
        result < 998244353,
{
    if i == n {
        10
    } else {
        let exp1 = if n - i - 1 >= 0 { (n - i - 1) as i64 } else { 0 };
        let pow1 = mod_pow(10, exp1, 998244353);
        let base_term = ((2u64 * 9u64 * pow1 as u64 * 10u64) % 998244353u64) as i64;
        
        let additional_term = if i < n - 1 {
            let exp2 = if n - i - 2 >= 0 { (n - i - 2) as i64 } else { 0 };
            let pow2 = mod_pow(10, exp2, 998244353);
            (((n - 1 - i) as u64 * 9u64 * 9u64 * pow2 as u64 * 10u64) % 998244353u64) as i64
        } else {
            0
        };
        
        ((base_term as u64 + additional_term as u64) % 998244353u64) as i64
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
    /* code modified by LLM (iteration 5): fixed loop invariants and overflow with proper bounds */
    let mut result: Vec<i8> = Vec::new();
    let mut i: i8 = 1;
    
    while i <= n
        invariant
            1 <= i <= n + 1,
            result.len() == (i - 1) as nat,
            i <= 127,
            n <= 30,
        decreases n - i
    {
        let block_val = compute_block_count(n, i);
        result.push(block_val as i8);
        i = (i as u8 + 1u8) as i8;
    }
    
    result
}
// </vc-code>


}

fn main() {}