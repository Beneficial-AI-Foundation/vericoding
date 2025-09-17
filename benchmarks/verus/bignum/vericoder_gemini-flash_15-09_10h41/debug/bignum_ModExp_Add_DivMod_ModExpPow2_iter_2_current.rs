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
/* helper modified by LLM (iteration 2): fixed type error in `res_final` definition */
spec fn subrange_to_seq(s: &[char], start: int, end: int) -> Seq<char>
  requires 0 <= start <= end <= s.len()
{
  s@.subrange(start, end)
}

proof fn bit_string_preserves_validity(s: Seq<char>, start: int, end: int)
  requires ValidBitString(s),
    0 <= start <= end <= s.len()
  ensures ValidBitString(s.subrange(start, end)) {}

proof fn prefix_mod_exp_lemma(
  sx_seq: Seq<char>,
  sy_seq: Seq<char>,
  sz_seq: Seq<char>,
  first_bit: char,
  rem_sy_seq: Seq<char>,
  res_rem: Seq<char>,
  res_final: Seq<char>,
  k: nat
)
  requires
    ValidBitString(sx_seq),
    ValidBitString(sy_seq),
    ValidBitString(sz_seq),
    sy_seq == rem_sy_seq.push(first_bit),
    Str2Int(sz_seq) > 1,
    res_rem == ModExp(sx_seq.view(), rem_sy_seq.view(), sz_seq.view())@,
    (first_bit == '0' || first_bit == '1'),
    res_final == (if first_bit == '0' {
      MulMod(res_rem.view(), res_rem.view(), sz_seq.view())@
    } else {
      MulMod(sx_seq.view(), MulMod(res_rem.view(), res_rem.view(), sz_seq.view()).view(), sz_seq.view())@
    }),
    Str2Int(rem_sy_seq) == k
  ensures
    Str2Int(res_final) == Exp_int(Str2Int(sx_seq), Str2Int(sy_seq)) % Str2Int(sz_seq)
{
  let base = Str2Int(sx_seq);
  let modulus = Str2Int(sz_seq);
  let rem_exp = Str2Int(res_rem);
  let current_exp = Str2Int(sy_seq);

  let rem_sy_val = Str2Int(rem_sy_seq);
  assert(rem_sy_val == k);
  assert(Str2Int(sy_seq) == 2 * rem_sy_val + (if first_bit == '1' { 1nat } else { 0nat }));

  // Need to prove this from the recursive call's ensures clause
  assert(rem_exp == Exp_int(base, rem_sy_val) % modulus);

  let term1 = (rem_exp * rem_exp) % modulus;
  let term2 = if first_bit == '0' {
    term1
  } else {
    (base * term1) % modulus
  };

  // proof for Exp_int(base, 2 * k)
  let exp_2k = Exp_int(base, 2 * k);
  assert(exp_2k == Exp_int(base, k) * Exp_int(base, k));

  // proof for Exp_int(base, 2 * k + 1)
  let exp_2k_plus_1 = Exp_int(base, 2 * k + 1);
  assert(exp_2k_plus_1 == base * Exp_int(base, 2*k));

  if first_bit == '0' {
    assert(current_exp == 2 * k);
    assert(Exp_int(base, current_exp) % modulus == (Exp_int(base, k) * Exp_int(base, k)) % modulus);
    assert(rem_exp == Exp_int(base, k) % modulus);
    assert((rem_exp * rem_exp) % modulus == (Exp_int(base, k) % modulus * Exp_int(base, k) % modulus) % modulus);
    assert((Exp_int(base, k) % modulus * Exp_int(base, k) % modulus) % modulus == (Exp_int(base, k) * Exp_int(base, k)) % modulus) by (nonlinear_arith);
    assert(term1 == Exp_int(base, current_exp) % modulus);
    assert(term2 == Exp_int(base, current_exp) % modulus);
  } else {
    assert(current_exp == 2 * k + 1);
    assert(Exp_int(base, current_exp) % modulus == (base * Exp_int(base, 2*k)) % modulus);
    assert(Exp_int(base, 2 * k) % modulus == (Exp_int(base, k) % modulus * Exp_int(base, k) % modulus) % modulus);
    assert(term1 == Exp_int(base, 2 * k) % modulus);
    assert((base * term1) % modulus == (base * Exp_int(base, 2 * k) % modulus) % modulus);
    assert(( base * Exp_int(base, 2 * k) % modulus) % modulus == (base * Exp_int(base, 2 * k)) % modulus) by (nonlinear_arith);
    assert(term2 == Exp_int(base, current_exp) % modulus);
  }

  assert(Str2Int(res_final) == Exp_int(base, current_exp) % modulus);
}

exec fn MulMod(s1: &[char], s2: &[char], sm: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), ValidBitString(sm@), Str2Int(sm@) > 0
  ensures ValidBitString(res@), Str2Int(res@) == (Str2Int(s1@) * Str2Int(s2@)) % Str2Int(sm@)
{
  let n1 = Str2Int(s1@);
  let n2 = Str2Int(s2@);
  let m = Str2Int(sm@);
  let product = n1 * n2;
  let remainder = product % m;
  let mut res_vec: Vec<char> = Vec::new();
  if remainder == 0 {
    res_vec.push('0');
  } else {
    let mut temp = remainder;
    while temp > 0
      invariant
        temp >= 0,
        ValidBitString(res_vec@)
      decreases temp
    {
      let bit = temp % 2;
      if bit == 0 {
        res_vec.insert(0, '0');
      } else {
        res_vec.insert(0, '1');
      }
      temp = temp / 2;
    }
  }
  res_vec
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
/* code modified by LLM (iteration 2): fixed syntax for if-expression */
{
  let base_val = Str2Int(sx@);
  let exp_val = Str2Int(sy@);
  let mod_val = Str2Int(sz@);

  if exp_val == 0 {
    let mut res_vec = Vec::new();
    res_vec.push('1');
    return res_vec;
  }

  let last_bit = sy@[sy@.len() as int - 1];
  let rem_sy_seq = sy@.subrange(0, sy@.len() as int - 1);

  let rem_sy_vec: Vec<char> = rem_sy_seq.to_vec();
  let rem_sy_slice = rem_sy_vec.as_slice();

  let res_rem_call = ModExp(sx, rem_sy_slice, sz);
  let res_rem_seq = res_rem_call@;

  let res_final_seq: Seq<char>;
  if last_bit == '0' {
    let temp_mul = MulMod(res_rem_call.as_slice(), res_rem_call.as_slice(), sz);
    res_final_seq = temp_mul@;
  } else {
    let temp_mul1 = MulMod(res_rem_call.as_slice(), res_rem_call.as_slice(), sz);
    let temp_mul2 = MulMod(sx, temp_mul1.as_slice(), sz);
    res_final_seq = temp_mul2@;
  }

  proof {
    bit_string_preserves_validity(sy@, 0, sy@.len() as int - 1);
    prefix_mod_exp_lemma(
      sx@,
      sy@,
      sz@,
      last_bit,
      rem_sy_seq,
      res_rem_call@,
      res_final_seq,
      Str2Int(rem_sy_seq)
    );
  }

  let mut res_final_vec = Vec::new();
  for i in 0..res_final_seq.len() {
    res_final_vec.push(res_final_seq.index(i));
  }
  res_final_vec
}
// </vc-code>

fn main() {}
}
