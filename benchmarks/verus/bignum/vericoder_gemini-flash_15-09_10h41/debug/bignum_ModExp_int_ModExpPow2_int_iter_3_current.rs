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
/* helper modified by LLM (iteration 3): Fix type errors for ModExpPow2_int and int_to_bitstring */
spec fn ModExpPow2_int(s_a: Seq<char>, s_b: Seq<char>, s_n: Seq<char>) -> nat
  requires ValidBitString(s_a), ValidBitString(s_b), ValidBitString(s_n), Str2Int(s_n) > 1
  decreases s_b.len()
{
  if s_b.len() == 0 {
    1
  } else {
    let a_int = Str2Int(s_a);
    let b_int = Str2Int(s_b);
    let n_int = Str2Int(s_n);

    if b_int == 0 {
      1
    } else if b_int % 2 == 0 {
      let half_b = b_int / 2;
      let recurse_result = ModExpPow2_int(s_a, int_to_bitstring(half_b), s_n);
      (recurse_result * recurse_result) % n_int
    } else {
      let half_b = b_int / 2;
      let recurse_result = ModExpPow2_int(s_a, int_to_bitstring(half_b), s_n);
      (a_int * recurse_result * recurse_result) % n_int
    }
  }
}
spec fn int_to_bitstring(i: nat) -> Seq<char>
  decreases i
{
  if i == 0 {
    seq!['0']
  } else {
    let mut result = Seq::new();
    let mut temp: nat = i;
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
/* code modified by LLM (iteration 3): Fix compilation errors: invalid suffix `nat` for literal numbers, `Seq::new()` arguments and type mismatches. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    let mut result_int: nat = 1;
    let mut base: nat = x_int % z_int;
    let mut exponent: nat = y_int;

    while exponent > 0
      invariant
        result_int * Exp_int(base, exponent) % z_int == Exp_int(x_int, y_int) % z_int,
        z_int > 1,
        exponent >= 0
      decreases exponent
    {
        if exponent % 2 == 1 {
            result_int = (result_int * base) % z_int;
        }
        base = (base * base) % z_int;
        exponent = exponent / 2;
    }

    let mut char_vec: Vec<char> = Vec::new();
    let mut temp: nat = result_int;

    if temp == 0 && z_int > 0 { 
      char_vec.push('0');
    } else {
      while temp > 0
        invariant
          temp >= 0
        decreases temp
      {
          if temp % 2 == 1 {
              char_vec.push('1');
          } else {
              char_vec.push('0');
          }
          temp = temp / 2;
      }
    }

    char_vec.reverse();
    char_vec
}
// </vc-code>

fn main() {}
}
