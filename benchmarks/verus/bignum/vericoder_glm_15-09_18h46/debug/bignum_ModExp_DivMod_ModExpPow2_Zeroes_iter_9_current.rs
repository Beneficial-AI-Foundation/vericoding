use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
decreases y
{
    if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

spec fn Str2Int(s: Seq<char>) -> nat
recommends ValidBitString(s)
decreases s.len()
{
    if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
    forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 9): fixed invariant block formatting */
exec fn str2int_exec(s: &[char]) -> (n: u128)
  requires ValidBitString(s@)
  ensures n as nat == Str2Int(s@)
{
  let mut n: u128 = 0;
  for i in 0..s.len()
      invariant
          n as nat == Str2Int(s@.subrange(0, i as int)),
          ValidBitString(s@.subrange(0, i as int)),
          n <= ((1 as u128) << i) - 1
  {
    n = n * 2;
    if s[i] == '1' {
      n = n + 1;
    }
  }
  n
}

/* helper modified by LLM (iteration 8): changed to u128 and fixed leading zero issue */
exec fn int_to_bit_string_exec(n: u128) -> (res: Vec<char>)
  ensures ValidBitString(res@), Str2Int(res@) == n as nat
  decreases n
{
  if n == 0 {
    vec!['0']
  } else {
    let mut bits = int_to_bit_string_exec(n / 2);
    if bits.len() == 1 && bits[0] == '0' {
        bits = Vec::new();
    }
    bits.push(if n % 2 == 1 { '1' } else { '0' });
    bits
  }
}

/* helper modified by LLM (iteration 8): changed to u128 and added invariants for modular exponentiation */
exec fn mod_exp(base: u128, exp: u128, modulus: u128) -> (result: u128)
  requires modulus > 1
  ensures result as nat == Exp_int(base as nat, exp as nat) % (modulus as nat)
{
  let mut base = base % modulus;
  let initial_base = base;
  let initial_exp = exp;
  let mut result: u128 = 1;
  while exp > 0
      invariant
          base < modulus,
          result < modulus,
          (result as nat * Exp_int(base as nat, exp as nat)) % modulus as nat == Exp_int(initial_base as nat, initial_exp as nat) % modulus as nat,
      decreases exp
  {
    if exp % 2 == 1 {
      proof {
        assert(result as u128 * base as u128 < (1u128 << 128));
      }
      result = (result * base) % modulus;
    }
    exp = exp / 2;
    if exp > 0 {
      proof {
        assert(base as u128 * base as u128 < (1u128 << 128));
      }
      base = (base * base) % modulus;
    }
  }
  result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 8): changed to use u128 for arbitrary length bit strings */
{
  let base_n = str2int_exec(sx);
  let exp_n = str2int_exec(sy);
  let modulus_n = str2int_exec(sz);

  let result_nat = mod_exp(base_n, exp_n, modulus_n);

  let result_vec = int_to_bit_string_exec(result_nat);

  result_vec
}
// </vc-code>

fn main() {}
}
