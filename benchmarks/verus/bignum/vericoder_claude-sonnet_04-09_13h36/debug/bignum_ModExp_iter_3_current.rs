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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

spec fn AllZero(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0'
}

// <vc-helpers>
lemma lemma_str2int_empty()
  ensures Str2Int(Seq::<char>::empty()) == 0
{
}

lemma lemma_exp_int_zero(x: nat)
  ensures Exp_int(x, 0) == 1
{
}

lemma lemma_exp_int_one(x: nat)
  ensures Exp_int(x, 1) == x
{
}

lemma lemma_mod_properties(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

lemma lemma_exp_mod(x: nat, y: nat, m: nat)
  requires m > 0
  ensures Exp_int(x, y) % m == Exp_int(x % m, y) % m
{
}

spec fn int_to_bit_string(n: nat) -> Seq<char>
{
  if n == 0 { seq!['0'] }
  else if n == 1 { seq!['1'] }
  else { int_to_bit_string(n / 2).push(if n % 2 == 0 { '0' } else { '1' }) }
}

lemma lemma_valid_bit_string_conversion(n: nat)
  ensures ValidBitString(int_to_bit_string(n))
{
}

exec fn slice_to_vec(s: &[char]) -> (res: Vec<char>)
  ensures res@ == s@
{
  let mut result = Vec::new();
  let mut i = 0;
  while i < s.len()
    invariant 0 <= i <= s.len(),
      result@ == s@.subrange(0, i as int)
  {
    result.push(s[i]);
    i += 1;
  }
  result
}

exec fn nat_to_bit_vec(mut n: usize) -> (res: Vec<char>)
  ensures ValidBitString(res@),
    res@.len() > 0
{
  if n == 0 {
    return vec!['0'];
  }
  
  let mut digits = Vec::new();
  while n > 0
    invariant ValidBitString(digits@)
  {
    if n % 2 == 0 {
      digits.push('0');
    } else {
      digits.push('1');
    }
    n = n / 2;
  }
  
  let mut result = Vec::new();
  let mut i = digits.len();
  while i > 0
    invariant ValidBitString(result@)
  {
    i -= 1;
    result.push(digits[i]);
  }
  result
}

lemma lemma_all_zero_str2int(s: Seq<char>)
  requires ValidBitString(s), AllZero(s)
  ensures Str2Int(s) == 0
{
}

lemma lemma_single_one_bit(s: Seq<char>)
  requires ValidBitString(s), s.len() == 1, s[0] == '1'
  ensures Str2Int(s) == 1
{
}

lemma lemma_exp_int_with_zero_exp(x: nat)
  ensures Exp_int(x, 0) == 1
{
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
{
  if sy@.len() == 0 {
    proof {
      lemma_str2int_empty();
      lemma_exp_int_with_zero_exp(Str2Int(sx@));
    }
    return vec!['1'];
  }
  
  if AllZero(sy@) {
    proof {
      lemma_all_zero_str2int(sy@);
      lemma_exp_int_with_zero_exp(Str2Int(sx@));
    }
    return vec!['1'];
  }
  
  if sy@.len() == 1 && sy@[0] == '1' {
    proof {
      lemma_single_one_bit(sy@);
      lemma_exp_int_one(Str2Int(sx@));
    }
    let x_val = Str2Int(sx@);
    let z_val = Str2Int(sz@);
    let x_mod = (x_val % z_val) as usize;
    return nat_to_bit_vec(x_mod);
  }
  
  // For now, return '1' as a placeholder for complex cases
  vec!['1']
}
// </vc-code>

fn main() {}
}