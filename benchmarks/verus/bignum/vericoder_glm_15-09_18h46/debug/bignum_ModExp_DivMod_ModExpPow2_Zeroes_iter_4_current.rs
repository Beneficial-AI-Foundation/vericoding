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
/* helper modified by LLM (iteration 4): changed nat to u64 for exec code */
exec fn str2int_exec(s: &[char]) -> (n: u64)
  requires ValidBitString(s@)
  ensures n as nat == Str2Int(s@)
{
  let mut n: u64 = 0;
  for i in 0..s.len()
    invariant n as nat == Str2Int(s@.subsequence(0, i as int))
  {
    n = n * 2;
    if s[i] == '1' {
      n = n + 1;
    }
  }
  n
}

/* helper modified by LLM (iteration 4): changed nat to u64 for exec code */
exec fn int_to_bit_string_exec(n: u64) -> (res: Vec<char>)
  ensures ValidBitString(res@), Str2Int(res@) == n as nat
  decreases n
{
  if n == 0 {
    vec!['0']
  } else {
    let mut bits = int_to_bit_string_exec(n / 2);
    bits.push(if n % 2 == 1 { '1' } else { '0' });
    bits
  }
}

/* helper modified by LLM (iteration 4): changed nat to u64 for exec code */
exec fn mod_exp(base: u64, exp: u64, modulus: u64) -> (result: u64)
  requires modulus > 1
  ensures result as nat == Exp_int(base as nat, exp as nat) % (modulus as nat)
{
  let mut base = base % modulus;
  let mut exp = exp;
  let mut result: u64 = 1;
  while exp > 0 {
    if exp % 2 == 1 {
      result = (result * base) % modulus;
    }
    exp = exp / 2;
    base = (base * base) % modulus;
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
{
  /* code modified by LLM (iteration 4): changed nat to u64 for exec code */
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
