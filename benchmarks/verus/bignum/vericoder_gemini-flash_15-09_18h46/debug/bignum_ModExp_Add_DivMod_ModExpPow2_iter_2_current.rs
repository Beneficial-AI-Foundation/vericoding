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
/* helper modified by LLM (iteration 2): Changed `int_to_bitstring` to work with `nat` and made it a `spec fn` */
spec fn int_to_bitstring(i: nat) -> Seq<char>
  decreases i
{
  if i == 0 { seq!['0'] } else if i == 1 { seq!['1'] } else {
    let rem = i % 2; // remainder
    let div = i / 2; // quotient
    let mut bitstring = int_to_bitstring(div);
    bitstring.push(if rem == 1 { '1' } else { '0' });
    bitstring
  }
}
spec fn Str2IntLe(s: Seq<char>, max_len: nat)
  recommends ValidBitString(s) && s.len() <= max_len
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * Str2IntLe(s.subrange(0, s.len() as int - 1), max_len) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

proof fn exp_to_pow2_is_pow2(n: nat) ensures Exp_int(2, n) == 1 << n
{
    if n == 0 {
    } else {
        exp_to_pow2_is_pow2((n - 1) as nat);
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
/* code modified by LLM (iteration 2): Converted `int_to_bitstring` into a `spec fn` and applied it to the results for conversion to `Vec<char>`. */
{
  let s_int = Str2Int(sx@);
  let y_int = Str2Int(sy@);

  if y_int == 0 {
    let result_vec = vec!['1'];
    return result_vec;
  }

  if y_int == 1 {
    let mut result_vec = Vec::new();
    for i in 0..sx.len() {
      result_vec.push(sx[i]);
    }
    return result_vec;
  }

  let (q, r_vec) = DivMod(sy, &seq!['1', '0'] as &[char]); // Divide s_y by 2
  let q_int = Str2Int(q@);
  let r_int = Str2Int(r_vec@);

  let temp_result_vec = ModExp(sx, &q, sz);
  let temp_result_int = Str2Int(temp_result_vec@);

  let sq_temp_result_int = Exp_int(temp_result_int, 2) % Str2Int(sz@);
  let sq_temp_result_vec = int_to_bitstring(sq_temp_result_int);

  if r_int == 1 {
    // y is odd
    let final_res_int = (sq_temp_result_int * s_int) % Str2Int(sz@);
    int_to_bitstring(final_res_int).to_vec()
  } else {
    // y is even
    sq_temp_result_vec.to_vec()
  }
}

// </vc-code>

fn main() {}
}
