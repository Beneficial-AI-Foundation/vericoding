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
/* code modified by LLM (iteration 2): Removed assertion, added appropriate invariants, and made minor fix to `result_vec` access logic */
{
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    let mut result_vec: Vec<char> = Vec::new();
    let mut carry: nat = 0; // Changed to nat
    let mut i = 0;

    while i < max_len || carry > 0
        invariant
            result_vec.len() <= i + 1,
            (forall |k: int| 0 <= k && k < result_vec.len() as int ==> (result_vec@[k] == '0' || result_vec@[k] == '1')),
            carry == 0 || carry == 1,
            i <= max_len + 1
        decreases max_len - i + carry as int
    {
        let mut digit1 = 0;
        if i < len1 {
            digit1 = if s1[len1 - 1 - i] == '1' { 1 } else { 0 };
        }

        let mut digit2 = 0;
        if i < len2 {
            digit2 = if s2[len2 - 1 - i] == '1' { 1 } else { 0 };
        }

        let sum = digit1 + digit2 + carry;
        carry = sum / 2;
        let current_digit = if sum % 2 == 1 { '1' } else { '0' };
        result_vec.insert(0, current_digit);
        i = i + 1;
    }
    
    // Remove leading zeros if the result is not just "0"
    while result_vec.len() > 1 && result_vec[0] == '0' {
        result_vec.remove(0);
    }
    result_vec
}
// </vc-code>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* helper modified by LLM (iteration 2): Implemented `int_to_bit_string` to convert a nat to a bit string. */
spec fn int_to_bit_string_spec(n: nat) -> Seq<char>
  decreases n
{
  if n == 0 { Seq::singleton('0') }
  else {
    let remainder = (n % 2) as char;
    let prefix = int_to_bit_string_spec(n / 2);
    if prefix == Seq::singleton('0') && n / 2 == 0 { // avoid leading zeros unless it's just '0'
        Seq::singleton(if remainder == 1 {'1'} else {'0'})
    } else {
      prefix + Seq::singleton(if remainder == 1 {'1'} else {'0'})
    }
  }
}

exec fn int_to_bit_string(n: nat) -> Vec<char>
{
  if n == 0 { return vec!['0']; }
  let mut res_vec = Vec::new();
  let mut current_n = n;
  while current_n > 0
    invariant
      current_n >= 0,
      (forall |k: int| 0 <= k && k < res_vec.len() as int ==> (res_vec@[k] == '0' || res_vec@[k] == '1'))
    decreases current_n
  {
    let remainder = (current_n % 2) as char;
    res_vec.insert(0, if remainder == 1 {'1'} else {'0'});
    current_n = current_n / 2;
  }
  res_vec
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
/* code modified by LLM (iteration 2): Used `int_to_bit_string` helper function to convert nat to bit string. */
{
    let n_sx = Str2Int(sx@);
    let n_sy = Str2Int(sy@);
    let n_sz = Str2Int(sz@);

    let mut result: nat = 1;
    let mut base: nat = n_sx % n_sz;
    let mut exponent: nat = n_sy;

    while exponent > 0
        invariant
            (base * base) % n_sz == (base * base) % n_sz,
            exponent <= n_sy,
            (result * Exp_int(base, exponent)) % n_sz == Exp_int(n_sx, n_sy) % n_sz // Error in original, should be based on initial n_sx
        decreases exponent
    {
        if (exponent % 2) == 1 {
            result = (result * base) % n_sz;
        }
        base = (base * base) % n_sz;
        exponent = exponent / 2;
    }
    int_to_bit_string(result)
}
// </vc-code>

fn main() {}
}


