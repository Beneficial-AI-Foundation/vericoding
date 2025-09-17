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
/* helper modified by LLM (iteration 2): Fix type mismatches in recursive calls by converting nat to Seq<char> */
spec fn ModExpPow2_int(s_a: Seq<char>, s_b: Seq<char>, s_n: Seq<char>) -> nat
  requires ValidBitString(s_a), ValidBitString(s_b), ValidBitString(s_n), Str2Int(s_n) > 1
  decreases s_b.len()
{
  if s_b.len() == 0 {
    1
  } else if s_b.index(0) == '0' {
    ModExpPow2_int(s_a.subrange(1, s_b.len() as int), int_to_bitstring(2 * Str2Int(s_a) % Str2Int(s_n)), s_n)
  } else {
    (Str2Int(s_a) * ModExpPow2_int(s_a.subrange(1, s_b.len() as int - 1), int_to_bitstring(2 * Str2Int(s_a) % Str2Int(s_n)), s_n)) % Str2Int(s_n)
  }
}
spec fn int_to_bitstring(i: nat) -> Seq<char>
  decreases i
{
  if i == 0 {
    seq!['0']
  } else {
    let mut result = Seq::new();
    let mut temp = i;
    while temp > 0
      invariant
        temp >= 0
      decreases temp
    {
      if temp % 2 == 1 {
        result = result.push('1');
      } else {
        result = result.push('0');
      }
      temp = temp / 2;
    }
    result.reverse()
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int_ModExpPow2_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fix type mismatches (nat vs int) and add missing `log_2` behavior for nat */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    let mut result_int: nat = 1nat;
    let mut base: nat = x_int % z_int;
    let mut exponent: nat = y_int;

    while exponent > 0
      invariant
        result_int * Exp_int(base, exponent) % z_int == Exp_int(x_int, y_int) % z_int,
        z_int > 1
      decreases exponent
    {
        if exponent % 2 == 1nat {
            result_int = (result_int * base) % z_int;
        }
        base = (base * base) % z_int;
        exponent = exponent / 2nat;
    }

    let mut char_vec: Vec<char> = Vec::new();
    let mut temp = result_int;

    if temp == 0nat && z_int > 0nat { 
      char_vec.push('0');
    } else {
      while temp > 0nat
        invariant
          temp >= 0nat
        decreases temp
      {
          if temp % 2 == 1nat {
              char_vec.push('1');
          } else {
              char_vec.push('0');
          }
          temp = temp / 2nat;
      }
    }

    char_vec.reverse();
    char_vec
}
// </vc-code>

fn main() {}
}
