// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 {
    0nat
  } else {
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 {
    1nat
  } else {
    x * exp_int(x, (y - 1) as nat)
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

spec fn all_zero(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0,
    sy.len() == n + 1,
    str2int(sz) > 1
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases n
{
  assume(false);
  unreached()
}

fn zeros(n: nat) -> (s: Seq<char>)
  ensures 
    s.len() == n,
    valid_bit_string(s),
    str2int(s) == 0,
    all_zero(s)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): [removed unused helper]*/
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
    sy.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@),
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): [fixed type error for k, changing it from `int` to `usize`] */
{
  let sx_spec = sx@;
  let sy_spec = sy@;
  let sz_spec = sz@;

  if sy_spec.len() == 1 && sy_spec.index(0) == '0' {
    // y = 0, x^0 mod Z = 1 mod Z
    let one_char_vec = vec!['1'];
    proof!{{
      assert(str2int(one_char_vec@) == 1);
      assert(exp_int(str2int(sx_spec), 0nat) == 1);
      assert(1nat % str2int(sz_spec) == 1 % str2int(sz_spec));
    }}
    return one_char_vec;
  } else if sy_spec.len() == 1 && sy_spec.index(0) == '1' {
    // y = 1, x^1 mod Z = x mod Z
    let x_mod_z = mod_exp_pow2(sx_spec, sy_spec.subrange(0, 1), 0nat, sz_spec);
    proof!{{
      assert(str2int(x_mod_z) == str2int(sx_spec) % str2int(sz_spec));
    }}
    return x_mod_z.to_vec();
  }

  let k = (sy_spec.len() - 1) as usize;
  let y_prime = sy_spec.subrange(0, k);
  let last_bit = sy_spec.index(k);

  let res_y_prime = mod_exp(sx, y_prime.to_vec(), sz);
  let x_pow_y_prime_val = str2int(res_y_prime@);

  let x_sq_mod_z_val: nat;
  let x_sq_mod_z_vec: Vec<char>;

  if last_bit == '0' {
    // If y is even, (X^(y'))^2 mod Z
    proof! {
      // x_pow_y_prime_val is (X^(Y')) mod Z
      // We need to compute (x_pow_y_prime_val * x_pow_y_prime_val) % str2int(sz)
      assert(str2int(y_prime) * 2 == str2int(sy_spec)); // This is what we are implicitly doing with y_prime and last_bit
      assert(exp_int(str2int(sx_spec), str2int(sy_spec)) == exp_int(exp_int(str2int(sx_spec), str2int(y_prime)), 2));
      assert(str2int(res_y_prime@) == exp_int(str2int(sx_spec), str2int(y_prime)) % str2int(sz_spec));
    }
    x_sq_mod_z_vec = mod_exp_pow2(res_y_prime@, seq!['1','0'], 1nat, sz_spec).to_vec(); // Simulate squaring via mod_exp_pow2(base, 2, modulus)
    x_sq_mod_z_val = str2int(x_sq_mod_z_vec@);
  } else {
    // If y is odd, ((X^(y'))^2 * X) mod Z
    proof! {
      assert(str2int(y_prime) * 2 + 1 == str2int(sy_spec));
      assert(exp_int(str2int(sx_spec), str2int(sy_spec)) == exp_int(exp_int(str2int(sx_spec), str2int(y_prime)), 2) * str2int(sx_spec));
      assert(str2int(res_y_prime@) == exp_int(str2int(sx_spec), str2int(y_prime)) % str2int(sz_spec));
    }
    let sqrt_comp = mod_exp_pow2(res_y_prime@, seq!['1','0'], 1nat, sz_spec);
    x_sq_mod_z_vec = mod_exp_pow2(sqrt_comp, seq!['1'], 0nat, sz_spec).to_vec(); // Multiply by X. base^(1)
    x_sq_mod_z_val = str2int(x_sq_mod_z_vec@);
  }

  proof! {

    let x_spec = str2int(sx_spec);
    let y_spec = str2int(sy_spec);
    let z_spec = str2int(sz_spec);
    let y_prime_spec = str2int(y_prime);

    assert(str2int(res_y_prime@) == exp_int(x_spec, y_prime_spec) % z_spec);

    if last_bit == '0' {
      assert(y_spec == y_prime_spec * 2);
      let base_val = exp_int(x_spec, y_prime_spec);
      let expected_val = (base_val * base_val) % z_spec;
      // assert(element_proof(x_sq_mod_z_vec@, str2int(res_y_prime@), z_spec) == expected_val);
      assert(x_sq_mod_z_val == expected_val);

    } else {
      assert(y_spec == y_prime_spec * 2 + 1);
      let base_val = exp_int(x_spec, y_prime_spec);
      let sq_val = (base_val * base_val) % z_spec;
      let final_expected_val = (sq_val * x_spec) % z_spec;

      let tmp_res = mod_exp_pow2(res_y_prime@, seq!['1','0'], 1nat, sz_spec);
      assert(str2int(tmp_res) == exp_int(str2int(res_y_prime@), 2) % z_spec);

      // assert(element_proof(x_sq_mod_z_vec@, str2int(tmp_res), z_spec) == final_expected_val);

      assert(str2int(x_sq_mod_z_vec@) == final_expected_val);
    }

    assert(x_sq_mod_z_val == exp_int(x_spec, y_spec) % z_spec);

  }

  x_sq_mod_z_vec
}
// </vc-code>


}

fn main() {}