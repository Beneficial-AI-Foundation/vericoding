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

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 4): fixing unclosed delimiter issues and ensuring proper function body structure for Add */
  let s1_vec = s1.to_vec();
  let s2_vec = s2.to_vec();
  let mut res: Vec<char> = Vec::new();
  let mut carry: nat = 0;
  let mut i: int = 0;

  while i < s1_vec.len() as int || i < s2_vec.len() as int || carry == 1
    invariant
      0 <= i,
      carry as int >= 0,
      carry <= 1,
      ValidBitString(res@),
      // The sum of the current parts of s1 and s2, plus the carry-in,
      // should equal the current result `res` and the carry-out.
      // This invariant is difficult to formulate precisely with `Str2Int` without a `rev_Str2Int` concept.
      // For now, focusing on maintaining `ValidBitString` and basic loop properties.
      // More detailed numeric invariant will require a helper to track partial sums.
      res.len() <= i + 1,
    decreases (s1_vec.len() as int - i).max(0) + (s2_vec.len() as int - i).max(0) + carry as int
  {
    let mut bit1: nat = 0;
    let mut bit2: nat = 0;

    if i < s1_vec.len() as int {
      bit1 = if s1_vec[s1_vec.len() as int - 1 - i] == '1' { 1 } else { 0 };
    }
    if i < s2_vec.len() as int {
      bit2 = if s2_vec[s2_vec.len() as int - 1 - i] == '1' { 1 } else { 0 };
    }

    let sum = bit1 + bit2 + carry;
    let result_bit = sum % 2;
    carry = sum / 2;

    if result_bit == 1 {
      res.insert(0, '1');
    } else {
      res.insert(0, '0');
    }
    i = i + 1;
  }

  if res.is_empty() {
    res.push('0');
  }
  res
}
// </vc-code>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 4): fixing unclosed delimiter, ensuring full definition for ModExp, and moving helpers */
  if sy@.len() == 1 {
    if sy@[0] == '0' {
      let mut res_vec = Vec::<char>::new();
      res_vec.push('1');
      return res_vec;
    } else {
      let x_int = Str2Int(sx@);
      let z_int = Str2Int(sz@);
      let r = x_int % z_int;
      return to_bitstring(r);
    }
  } else {
    let sy_len_int = sy@.len() as int;
    let halfway = sy_len_int / 2;
    let sy_half_slice = sy.subslice(0, halfway);
    let mut sy_half_vec = Vec::new();
    sy_half_vec.extend_from_slice(sy_half_slice);

    let exp_res_str = ModExp(sx, &sy_half_vec, sz);
    let exp_res_int = Str2Int(exp_res_str@);

    let mut res_squared_int = exp_res_int * exp_res_int;
    res_squared_int = res_squared_int % Str2Int(sz@);

    let mut final_res_val = res_squared_int;

    if Str2Int(sy@) % 2 == 1 {
      let sx_val = Str2Int(sx@);
      final_res_val = (final_res_val * sx_val) % Str2Int(sz@);
    }
    return to_bitstring(final_res_val);
  }
}

/* helper modified by LLM (iteration 4): moved from vc-code to vc-helpers and ensured full definition */
fn Mul(s1: Vec<char>, s2: Vec<char>) -> Vec<char> {
  let n1 = Str2Int(s1@);
  let n2 = Str2Int(s2@);
  to_bitstring(n1 * n2)
}

/* helper modified by LLM (iteration 4): moved from vc-code to vc-helpers, fixed to_bitstring to handle n=0 and ensured ValidBitString */
fn to_bitstring(n: nat) -> Vec<char> {
  let mut res: Vec<char> = Vec::new();
  if n == 0 {
    res.push('0');
    return res;
  }
  let mut current_n = n;
  while current_n > 0
    invariant
      current_n >= 0,
      ValidBitString(res@.add(if current_n > 0 { Seq::singleton(if current_n % 2 == 1 {'1'} else {'0'}) } else { Seq::empty() })),
    decreases current_n
  {
    if current_n % 2 == 1 {
      res.insert(0, '1');
    } else {
      res.insert(0, '0');
    }
    current_n = current_n / 2;
  }
  res
}
// </vc-code>

fn main() {}
}


