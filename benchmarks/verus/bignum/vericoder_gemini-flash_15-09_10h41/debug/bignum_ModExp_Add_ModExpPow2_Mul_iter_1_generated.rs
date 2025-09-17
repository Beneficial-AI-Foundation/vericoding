use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
spec fn Add(s1: Seq<char>, s2: Seq<char>) -> Seq<char>
  requires
    ValidBitString(s1),
    ValidBitString(s2),
  ensures
    ValidBitString(result),
    Str2Int(result) == Str2Int(s1) + Str2Int(s2),
  decreases s1.len() + s2.len()
{
  if s1.len() == 0 && s2.len() == 0 {
    seq![]
  } else if s1.len() == 0 {
    s2
  } else if s2.len() == 0 {
    s1
  } else {
    let val1 = (s1.last() == '1') as nat;
    let val2 = (s2.last() == '1') as nat;
    let sum = val1 + val2;
    let carry = if sum >= 2 { '1' } else { '0' };
    let current_bit = if sum % 2 == 1 { '1' } else { '0' };

    let s1_prefix = s1.subrange(0, (s1.len() as int - 1) as nat);
    let s2_prefix = s2.subrange(0, (s2.len() as int - 1) as nat);

    let mut next_s2_prefix;
    if carry == '1' {
      next_s2_prefix = Add(s2_prefix, seq!['1']);
    } else {
      next_s2_prefix = s2_prefix;
    }
    let recursive_sum = Add(s1_prefix, next_s2_prefix);
    recursive_sum.add(current_bit)
  }
}

spec fn ModExp(base: Seq<char>, exp: Seq<char>, modulus_exp: nat) -> Seq<char>
  requires
    ValidBitString(base),
    ValidBitString(exp),
    modulus_exp > 0,
  ensures
    ValidBitString(result),
  decreases exp.len(), Str2Int(exp)
{
  if Str2Int(exp) == 0 {
    seq!['1']
  } else if Str2Int(exp) % 2 == 0 {
    let new_exp_bits = DivideByTwo(exp);
    let half_power = ModExp(base, new_exp_bits, modulus_exp);
    let squared = Multiply(half_power, half_power);
    Mod(squared, modulus_exp)
  } else {
    let new_exp_bits = DivideByTwo(exp);
    let half_power = ModExp(base, new_exp_bits, modulus_exp);
    let squared = Multiply(half_power, half_power);
    let multiplied = Multiply(squared, base);
    Mod(multiplied, modulus_exp)
  }
}

spec fn Multiply(s1: Seq<char>, s2: Seq<char>) -> Seq<char>
  requires
    ValidBitString(s1),
    ValidBitString(s2),
  ensures
    ValidBitString(result),
    Str2Int(result) == Str2Int(s1) * Str2Int(s2),
  decreases s2.len(), Str2Int(s2)
{
  if Str2Int(s2) == 0 {
    seq!['0']
  } else if Str2Int(s2) == 1 {
    s1
  } else if Str2Int(s2) % 2 == 0 {
    let half_s2 = DivideByTwo(s2);
    let multiplied_half = Multiply(s1, half_s2);
    Add(multiplied_half, multiplied_half)
  } else {
    let prev_s2 = Subtract(s2, seq!['1']);
    Add(s1, Multiply(s1, prev_s2))
  }
}

spec fn Mod(s: Seq<char>, modulus_exp: nat) -> Seq<char>
  requires
    modulus_exp > 0,
    ValidBitString(s),
  ensures ValidBitString(result)
{
  let modulus_val = 1_nat << modulus_exp;
  let val = Str2Int(s) % modulus_val;
  Int2Str(val, modulus_exp)
}

spec fn DivideByTwo(s: Seq<char>) -> Seq<char>
  requires ValidBitString(s)
  ensures
    ValidBitString(result),
    Str2Int(result) == Str2Int(s) / 2,
{
  if s.len() == 0 || (s.len() == 1 && s.index(0) == '0') {
    seq!['0']
  } else {
    s.subrange(0, (s.len() as int - 1) as nat)
  }
}

spec fn Subtract(s1: Seq<char>, s2: Seq<char>) -> Seq<char>
  requires
    ValidBitString(s1),
    ValidBitString(s2),
    Str2Int(s1) >= Str2Int(s2),
  ensures
    ValidBitString(result),
    Str2Int(result) == Str2Int(s1) - Str2Int(s2),
  decreases s1.len() + s2.len()
{
  if Str2Int(s2) == 0 {
    s1
  } else {
    if s1.len() == 0 {
      // This case should not happen if Str2Int(s1) >= Str2Int(s2) and Str2Int(s2) > 0
      seq!['0']
    } else {
      let val1 = (s1.last() == '1') as nat;
      let val2 = (s2.last() == '1') as nat;

      let prev_s1 = s1.subrange(0, s1.len() as int - 1);
      let prev_s2 = s2.subrange(0, s2.len() as int - 1);

      if val1 >= val2 {
        let current_bit = if val1 - val2 == 1 { '1' } else { '0' };
        (Subtract(prev_s1, prev_s2)).add(current_bit)
      } else {
        // val1 < val2, so we need to borrow from prev_s1
        let borrowed_s1 = Subtract(prev_s1, seq!['1']);
        let current_bit = if (val1 + 2) - val2 == 1 { '1' } else { '0' };
        (Subtract(borrowed_s1, prev_s2)).add(current_bit)
      }
    }
  }
}

spec fn Int2Str(n: nat, len_hint: nat) -> Seq<char>
  decreases len_hint
  ensures 
    ValidBitString(result),
    Str2Int(result) == n
{
  if n == 0 {
    if len_hint == 0 { seq![] } else { seq!['0'] }
  } else {
    let current_bit = if n % 2 == 1 { '1' } else { '0' };
    let remainder_seq = Int2Str(n / 2, len_hint - 1);
    remainder_seq.add(current_bit)
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
  let s_a = a@;
  let s_b = b@;

  let val_a = Str2Int(s_a);
  let val_b = Str2Int(s_b);

  let modulus_exp = s_b.len();

  let mod_exp_result = ModExp(s_a, s_b, modulus_exp);
  
  let final_result = Vec::from_seq(mod_exp_result);
  final_result
}
// </vc-code>

fn main() {}
}

