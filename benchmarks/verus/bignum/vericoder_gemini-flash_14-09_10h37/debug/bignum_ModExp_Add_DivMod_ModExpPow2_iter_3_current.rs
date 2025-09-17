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

exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
{
  assume(false);
  return Vec::<char>::new();
}

exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
{
  assume(false);
  return (Vec::<char>::new(), Vec::<char>::new());
}

exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
{
  assume(false);
  return Vec::<char>::new();
}

// <vc-helpers>
/* helper modified by LLM (iteration 3): int_to_bit_string_padded now returns a Vec<char> directly */
spec fn int_to_bit_string_padded(val: nat, pad_len: nat) -> Seq<char>
  ensures ValidBitString(result), result.len() == pad_len, Str2Int(result) == val
{
  let s = if val == 0 { Seq::singleton('0') } else { 
    let mut bits: Seq<char> = Seq::empty();
    let mut temp = val;
    while temp > 0
      invariant temp >= 0,
      decreases temp
    {
      if temp % 2 == 1 {
        bits = Seq::singleton('1').add(bits);
      } else {
        bits = Seq::singleton('0').add(bits);
      }
      temp = temp / 2;
    }
    bits
  };
  if s.len() < pad_len {
    let mut padded_s = Seq::new(pad_len, |i| '0');
    for i in 0..s.len() {
      padded_s = padded_s.update((pad_len - s.len() + i) as int, s.index(i as int));
    }
    padded_s
  } else if s.len() > pad_len {
    s.subrange((s.len() - pad_len) as int, s.len() as int)
  } else {
    s
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed indexing with `as int` for `subrange` and `index`, replaced placeholder `int_to_bit_string_padded` with a call to the new helper and removed one of the return values. */
{
  let s_x = sx@;
  let s_y = sy@;
  let s_z = sz@;

  if s_y.len() == 1 {
    if s_y.index(0) == '0' {
      return vec!['1']; // x^0 mod z = 1 mod z
    } else {
      // s_y is "1", so y=1
      // x^1 mod z = x mod z
      let (q, r) = DivMod(sx, sz);
      return r;
    }
  }

  let k: usize = s_y.len() - 1;
  let s_y_prime = s_y.subrange(0, k as int);
  let y_prime_char = s_y.index(k as int);

  let r_prime_vec = ModExp(sx, &s_y_prime.to_vec(), sz);
  let r_prime = r_prime_vec@;

  let s_x_int = Str2Int(s_x);
  let r_prime_int = Str2Int(r_prime);
  let s_z_int = Str2Int(s_z);

  if y_prime_char == '0' {
    // y = 2 * y'
    // x^y mod z = (x^(y'))^2 mod z
    let val_int = (r_prime_int * r_prime_int) % s_z_int;
    int_to_bit_string_padded(val_int, s_z.len() as nat).to_vec()
  } else {
    // y = 2 * y' + 1
    // x^y mod z = (x^(y'))^2 * x mod z
    let val_int = ((r_prime_int * r_prime_int) % s_z_int * s_x_int) % s_z_int;
    int_to_bit_string_padded(val_int, s_z.len() as nat).to_vec()
  }
}
// </vc-code>

fn main() {}
}
