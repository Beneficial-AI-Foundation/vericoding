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
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    let mut result_vec = Vec::new();
    let mut carry: nat = 0;
    let mut i: int = 0;

    while i < max_len || carry == 1
        invariant
            result_vec.len() == i as nat,
            carry == 0 || carry == 1,
            (Str2Int(s1@.subrange(0, i)) + Str2Int(s2@.subrange(0, i)) + @carry) == Str2Int(result_vec@) + Str2Int(Seq::new().push_array(&['0'; 1]).subrange(0,0)) + @carry * Exp_int(2, i as nat),
            forall |j: int| 0 <= j && j < result_vec.len() ==> (result_vec@[j] == '0' || result_vec@[j] == '1'),
            // For the assertion above the right Str2Int, the empty sequence returns 0, otherwise the Exp_int(2, i as nat) should be scaled
        decreases max_len - i
    {
        let bit1 = if i < len1 && s1@[len1 - 1 - i] == '1' { 1nat } else { 0nat };
        let bit2 = if i < len2 && s2@[len2 - 1 - i] == '1' { 1nat } else { 0nat };
        let sum = bit1 + bit2 + carry;

        let current_bit = if sum % 2 == 1 { '1' } else { '0' };
        carry = sum / 2;

        result_vec.push(current_bit);
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
{
    if Str2Int(sy@) == 0 {
        let mut res = Vec::new();
        if Str2Int(sx@) == 0 { // 0^0 mod N is usually 1, but depends on context. Here, we assume 1.
            res.push('1');
        } else {
             res.push('1');
        }
        return res;
    }

    let mut x_val = Str2Int(sx@);
    let mut y_val = n as nat;
    let mut z_val = Str2Int(sz@);

    let mut result: nat = 1;
    let mut base: nat = x_val % z_val;

    while y_val > 0
        invariant
            z_val > 1,
            base < z_val,
            result < z_val,
            (Exp_int(x_val, n as nat) % z_val) == (result * Exp_int(base, y_val)) % z_val,
            y_val >= 0
        decreases y_val
    {
        if y_val % 2 == 1 {
            result = (result * base) % z_val;
        }
        base = (base * base) % z_val;
        y_val = y_val / 2;
    }
    
    let mut current_val = result;
    let mut res_vec = Vec::new();
    if current_val == 0 {
        res_vec.push('0');
        return res_vec;
    }
    while current_val > 0
        invariant
            result == Str2Int(res_vec@) + current_val * Exp_int(2, res_vec.len() as nat),
            forall |j: int| 0 <= j && j < res_vec.len() ==> (res_vec@[j] == '0' || res_vec@[j] == '1'),
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


