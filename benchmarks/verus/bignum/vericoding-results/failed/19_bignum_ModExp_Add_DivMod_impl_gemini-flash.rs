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
/* code modified by LLM (iteration 10): Removed assumption and added initial logic. The loop invariants need to be fixed for correctness. */
{
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    let mut result_vec = Vec::new();
    let mut carry: nat = 0;
    let mut i = 0;

    while i < max_len || carry > 0
        invariant
            i <= max_len + 1,
            (forall |k: int| 0 <= k && k < result_vec.len() as int ==> (result_vec@[k] == '0' || result_vec@[k] == '1')),
            carry == 0 || carry == 1
        decreases max_len + 1 - i
    {
        let mut digit1: nat = 0;
        if i < len1 {
            digit1 = if s1[len1 - 1 - i] == '1' { 1 } else { 0 };
        }

        let mut digit2: nat = 0;
        if i < len2 {
            digit2 = if s2[len2 - 1 - i] == '1' { 1 } else { 0 };
        }

        let sum = digit1 + digit2 + carry;
        carry = sum / 2;
        let current_digit = if sum % 2 == 1 { '1' } else { '0' };
        result_vec.push(current_digit);
        i = i + 1;
    }
    
    result_vec.reverse();

    while result_vec.len() > 1 && result_vec[0] == '0'
      invariant
        result_vec.len() >= 1,
        (forall |k: int| 0 <= k && k < result_vec.len() as int ==> (result_vec@[k] == '0' || result_vec@[k] == '1'))
      decreases result_vec.len()
    {
        assert(result_vec.len() > 0);
        result_vec.remove(0);
    }

    if result_vec.is_empty() {
        result_vec.push('0');
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
/* helper modified by LLM (iteration 10): Corrected the definition to be a function. */
fn int_to_bit_string(n: nat) -> Vec<char>
  ensures ValidBitString(result@), Str2Int(result@) == n
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
    let remainder = current_n % 2;
    res_vec.push(if remainder == 1 { '1' } else { '0' });
    current_n = current_n / 2;
  }
  res_vec.reverse();
  res_vec
}

/* code modified by LLM (iteration 10): DivMod implementation depends on the int_to_bit_string helper. */
{
  let n_dividend = Str2Int(dividend@);
  let n_divisor = Str2Int(divisor@);

  let quotient = n_dividend / n_divisor;
  let remainder = n_dividend % n_divisor;
  
  (int_to_bit_string(quotient), int_to_bit_string(remainder))
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
/* code modified by LLM (iteration 10): Final Refinement of ModExp. */
{
    let n_sx = Str2Int(sx@);
    let n_sy = Str2Int(sy@);
    let n_sz = Str2Int(sz@);

    let mut result: nat = 1;
    let mut base: nat = n_sx % n_sz;
    let mut exponent: nat = n_sy;

    while exponent > 0
        invariant
            0 <= exponent,
            (result * Exp_int(base, exponent)) % n_sz == Exp_int(n_sx, n_sy) % n_sz // This invariant correctly tracks the relation between current values and the target.
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


