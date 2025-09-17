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
    let len1_usize = s1.len();
    let len2_usize = s2.len();
    let len1: usize = len1_usize;
    let len2: usize = len2_usize;
    let max_len: usize = if len1 > len2 { len1 } else { len2 };
    
    let mut result_vec = Vec::new();
    let mut carry: u8 = 0;
    let mut i: usize = 0;

    while i < max_len || carry == 1
        invariant
            carry == 0 || carry == 1,
            i >= result_vec.len(),
            forall |j: int| 0 <= j && j < result_vec.len() as int ==> (result_vec@[j] == '0' || result_vec@[j] == '1'),
        decreases (max_len as int) - (i as int)
    {
        let bit1_val: u8 = if i < len1 && s1@[len1 - 1 - i] == '1' { 1 } else { 0 };
        let bit2_val: u8 = if i < len2 && s2@[len2 - 1 - i] == '1' { 1 } else { 0 };
        let sum: u8 = bit1_val + bit2_val + carry;

        let current_bit_char = if sum % 2 == 1 { '1' } else { '0' };
        carry = sum / 2;

        result_vec.push(current_bit_char);
        i = i + 1;
    }

    result_vec.reverse();
    result_vec
}
// </vc-code>

// <vc-spec>
exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 8): No changes, previous fix was sufficient. */
{
    // Handle the case where sy represents 0 (x^0 = 1)
    if Str2Int(sy@) == 0 {
        let mut res = Vec::new();
        res.push('1');
        return res;
    }

    let x_val = Str2Int(sx@);
    let y_spec_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);

    let mut result: nat = 1;
    let mut base: nat = x_val % z_val;
    let mut exponent: nat = y_spec_val;

    while exponent > 0
        invariant
            z_val > 1,
            base < z_val,
            result < z_val,
            (Exp_int(x_val, y_spec_val) % z_val) == (result * Exp_int(base, exponent)) % z_val,
            exponent >= 0
        decreases exponent
    {
        if exponent % 2 == 1 {
            result = (result * base) % z_val;
        }
        base = (base * base) % z_val;
        exponent = exponent / 2;
    }

    // Convert the result (nat) to a bit string (Vec<char>)
    let mut res_vec = Vec::new();
    if result == 0 {
        res_vec.push('0');
        return res_vec;
    }

    let mut current_val: nat = result;
    while current_val > 0
        invariant
            result == Str2Int(res_vec@.reverse()) + current_val * Exp_int(2, res_vec.len() as nat),
            forall |j: int| 0 <= j && j < res_vec.len() as int ==> (res_vec@[j] == '0' || res_vec@[j] == '1'),
            current_val >= 0
        decreases current_val
    {
        if current_val % 2 == 1 {
            res_vec.push('1');
        } else {
            res_vec.push('0');
        }
        current_val = current_val / 2;
    }
    res_vec.reverse();
    res_vec
}
// </vc-code>

fn main() {}
}


