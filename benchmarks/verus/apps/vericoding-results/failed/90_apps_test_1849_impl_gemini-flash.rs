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
/* helper modified by LLM (iteration 5): Fixed compilation error by replacing `integer_pow(base, exp, modulus) as int < modulus as int` with `integer_pow(base, exp, modulus) < modulus` because `integer_pow` returns `i8`, not `int`. */
proof fn lemma_pow_is_i8_compatible(base: i8, exp: i8, modulus: i8)
  requires
    base as int >= 0,
    exp as int >= 0,
    modulus as int > 0 && modulus as int <= 127,
    base as int == 10
  ensures
    pow(base as int, exp as int, modulus as int) == integer_pow(base, exp, modulus) as int,
    integer_pow(base, exp, modulus) as int >= 0,
    integer_pow(base, exp, modulus) < modulus
  decreases exp
{
  if exp == 0 {
    assert(integer_pow(base, exp, modulus) == 1i8);
    assert(pow(base as int, exp as int, modulus as int) == 1int);
  } else {
    lemma_pow_is_i8_compatible(base, (exp - 1) as i8, modulus);
    let prev_pow_i8 = integer_pow(base, (exp - 1) as i8, modulus);
    let prev_pow_int = pow(base as int, (exp - 1) as int, modulus as int);
    assert(prev_pow_i8 as int == prev_pow_int);
    let current_pow_i8_val = (base as i128 * prev_pow_i8 as i128) % modulus as i128;
    assert(integer_pow(base, exp, modulus) as i128 == current_pow_i8_val);
    let current_pow_int_val = (base as int * prev_pow_int) % modulus as int;
    assert(pow(base as int, exp as int, modulus as int) == current_pow_int_val);
    assert(current_pow_i8_val == current_pow_int_val as i128);
  }
}

pub fn integer_pow(base: i8, exp: i8, modulus: i8) -> i8
  requires
    base as int >= 0,
    exp as int >= 0,
    modulus as int > 0,
    modulus as int <= 127
  ensures
    integer_pow(base, exp, modulus) as int == pow(base as int, exp as int, modulus as int),
    integer_pow(base, exp, modulus) >= 0,
    integer_pow(base, exp, modulus) < modulus
  decreases exp
{
  if exp == 0 { 1i8 }
  else {
    let res = (base as i128 * integer_pow(base, (exp - 1) as i8, modulus) as i128) % modulus as i128;
    res as i8
  }
}

pub fn integer_block_count_formula(n_i8: i8, i_i8: i8) -> i8
  requires
    n_i8 as int >= 1,
    1 <= i_i8 as int <= n_i8 as int,
    MOD <= 127
  ensures
    integer_block_count_formula(n_i8, i_i8) as int == block_count_formula(n_i8 as int, i_i8 as int),
    integer_block_count_formula(n_i8, i_i8) >= 0,
    integer_block_count_formula(n_i8, i_i8) < MOD as i8
{
  let n = n_i8 as int;
  let i = i_i8 as int;

  if i == n {
    proof {
      /* lemma_block_count_formula_non_negative(n, i); */ // This lemma does not exist in the context provided
    }
    10i8
  } else {
    let exp1 = (n - i - 1) as i8;
    let pow1_val: i8;
    if exp1 >= 0 {
        pow1_val = integer_pow(10i8, exp1, MOD as i8);
        proof {
            lemma_pow_is_i8_compatible(10i8, exp1, MOD as i8);
        }
    } else {
        pow1_val = 1i8;
        proof {
            assert(pow(10, exp1 as int, MOD) == 1);
        }
    }

    let term1_val: i128 = (2i128 * 9i128 * pow1_val as i128 * 10i128);
    let term1_mod = term1_val % MOD as i128;

    let term2_mod_i128: i128;
    if i < n - 1 {
      let exp2 = (n - i - 2) as i8;
      let pow2_val: i8;
      if exp2 >= 0 {
          pow2_val = integer_pow(10i8, exp2, MOD as i8);
          proof {
              lemma_pow_is_i8_compatible(10i8, exp2, MOD as i8);
          }
      } else {
          pow2_val = 1i8;
          proof {
              assert(pow(10, exp2 as int, MOD) == 1);
          }
      }
      let term2_val: i128 = ((n - 1 - i) as i128 * 9i128 * 9i128 * pow2_val as i128 * 10i128);
      term2_mod_i128 = term2_val % MOD as i128;
    } else {
      term2_mod_i128 = 0i128;
    }
    proof {
      /* lemma_block_count_formula_non_negative(n, i); */ // This lemma does not exist in the context provided
      assert(block_count_formula(n, i) as i128 == (term1_mod + term2_mod_i128) % MOD as i128);
    }
    ((term1_mod + term2_mod_i128) % MOD as i128) as i8
  }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<i8>)
  requires valid_input(n as int)
  ensures valid_result(result@.map(|_index: int, x: i8| x as int), n as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected `result.vec_nth(k)` to `result.dom_nth(k)` within forall quantifiers to fix type mismatch, because `result.vec_nth(k)` returns `Option<i8>` while `result.dom_nth(k)` returns `i8`. */
{
  let n_int = n as int;
  let mut result: Vec<i8> = Vec::new();
  result.reserve(n_int as usize);

  let mut i: int = 1;

  while i <= n_int
    invariant
      result.len() == (i - 1) as nat,
      i >= 1,
      i <= n_int + 1,
      n_int >= 1,
      (forall|k: int| 0 <= k < result.len() ==> #[trigger] result.dom_nth(k) as int >= 0 && #[trigger] result.dom_nth(k) as int < MOD),
      (forall|k: int| 0 <= k < result.len() ==> #[trigger] result.dom_nth(k) as int == block_count_formula(n_int, (k + 1) as int))
  {
    if i == n_int {
      result.push(10i8);
      proof {
        /* lemma_block_count_formula_non_negative(n_int, i); */ // This lemma does not exist in the context provided
        assert(result.dom_nth(i - 1) == 10i8);
        assert( result.dom_nth(i - 1) as int == block_count_formula(n_int, i));
        assert( result.dom_nth(i - 1) as int >= 0 );
        assert( result.dom_nth(i - 1) as int < MOD );
      }
    } else {
      let block_val = integer_block_count_formula(n, i as i8);
      result.push(block_val);
      proof {
        /* lemma_block_count_formula_non_negative(n_int, i); */ // This lemma does not exist in the context provided
        // assert designator result.vec_nth(i - 1), result.vec_nth(i - 1).is_Some(); // This assertion was for `vec_nth` which is not `dom_nth`
        assert(result.dom_nth(i - 1) == block_val);
        assert(result.dom_nth(i - 1) as int == block_count_formula(n_int, i));
        assert(result.dom_nth(i - 1) as int >= 0 );
        assert(result.dom_nth(i - 1) as int < MOD );
      }
    }
    i = i + 1;
  }

  result
}
// </vc-code>


}

fn main() {}