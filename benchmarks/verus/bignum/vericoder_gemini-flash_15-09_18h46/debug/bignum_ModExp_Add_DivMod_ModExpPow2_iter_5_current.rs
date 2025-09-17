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
spec fn int_to_bitstring(i: nat) -> Seq<char> /* helper modified by LLM (iteration 5): Fixed Seq::singleton to Seq::new(x) */ { if i == 0 { Seq::new(&['0']) } else { let mut res = Seq::empty(); let mut temp = i; while temp > 0 invariant res.len() >= 0, temp >= 0, temp@ <= i@ decreases temp { if temp % 2 == 1 { res = Seq::new(&['1']) + res; } else { res = Seq::new(&['0']) + res; } temp = temp / 2; } res } }
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
/* code modified by LLM (iteration 5): Fixed integer literals with `nat` suffix, and Seq to Vec conversion. */ {
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

  let two_char_array: &[char] = &['1', '0'];
  let (q, r_vec) = DivMod(sy, two_char_array);
  let q_int = Str2Int(q@);
  let r_int = Str2Int(r_vec@);

  let temp_result_vec = ModExp(sx, &q, sz);
  let temp_result_int = Str2Int(temp_result_vec@);

  let sz_int = Str2Int(sz@);
  let sq_temp_result_int: nat = Exp_int(temp_result_int, 2) % sz_int as nat;
  let sq_temp_result_seq = int_to_bitstring(sq_temp_result_int);

  if r_int == 1 {
    let final_res_int: nat = (sq_temp_result_int * s_int) % sz_int;
    int_to_bitstring(final_res_int).to_vec()
  } else {
    sq_temp_result_seq.to_vec()
  }
}
// </vc-code>

fn main() {}
}
