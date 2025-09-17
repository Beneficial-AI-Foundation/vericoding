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
/* code modified by LLM (iteration 9): Updated loop invariant for result_vec content and length. */
{
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    let mut result_vec: Vec<char> = Vec::new();
    let mut carry: nat = 0;

    let mut i: usize = 0;
    while i < max_len + 1 || carry == 1
        invariant
            0 <= i as int,
            (i as int) <= (max_len as int) + 1,
            carry == 0 || carry == 1,
            (forall |k: int| 0 <= k && k < result_vec.len() ==> (result_vec.index(k) == '0' || result_vec.index(k) == '1')),
        decreases (max_len as int + 1) - (i as int)
    {
        let bit1 = if i < len1 { if s1[len1 - 1 - i] == '1' { 1nat } else { 0nat } } else { 0nat };
        let bit2 = if i < len2 { if s2[len2 - 1 - i] == '1' { 1nat } else { 0nat } } else { 0nat };
        let sum = bit1 + bit2 + carry;

        let current_bit = sum % 2;
        carry = sum / 2;

        result_vec.insert(0, if current_bit == 1 { '1' } else { '0' });
        i = i + 1;
    }

    if result_vec.is_empty() {
        result_vec.push('0');
    }
    result_vec
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): Fixed type error with Exp_int argument. */
{
    let len1 = s1.len();
    let len2 = s2.len();
    let val1 = Str2Int(s1@);
    let val2 = Str2Int(s2@);
    let mut result_vec: Vec<char> = Vec::new();

    if val1 == 0 || val2 == 0 {
        result_vec.push('0');
        return result_vec;
    }

    let mut product: nat = 0;
    let mut i: usize = 0;

    while i < len2
        invariant
            0 <= i as int,
            i <= len2,
        decreases len2 - i
    {
        let bit2 = if s2[len2 - 1 - i] == '1' { 1nat } else { 0nat };
        if bit2 == 1 {
            product = product + (val1 * Exp_int(2, i as nat));
        }
        i = i + 1;
    }

    proof {
        assert(product == val1 * val2);
    }

    let mut temp_product = product;
    while temp_product > 0
        invariant
            (forall |k: int| 0 <= k && k < result_vec.len() ==> (result_vec.index(k) == '0' || result_vec.index(k) == '1')),
        decreases temp_product
    {
        if temp_product % 2 == 1 {
            result_vec.insert(0, '1');
        } else {
            result_vec.insert(0, '0');
        }
        temp_product = temp_product / 2;
    }

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
/* code modified by LLM (iteration 9): Updated loop invariant for result_vec content and length. */
{
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let z = Str2Int(sz@);

    let mut res_val: nat = 1; // x^0 mod z

    if y == 0 {
        let mut result_vec: Vec<char> = Vec::new();
        result_vec.push('1');
        return result_vec;
    }

    let base = x % z;
    
    res_val = base;
    let mut i: usize = 0;
    while i < n as usize
        invariant
            0 <= i as int,
            (i as int) <= n,
            res_val == Exp_int(base, Exp_int(2, i as nat)) % z,
        decreases n - (i as int)
    {
        res_val = (res_val * res_val) % z;
        i = i + 1;
    }

    let mut result_vec: Vec<char> = Vec::new();
    if res_val == 0 {
        result_vec.push('0');
        return result_vec;
    }

    let mut temp_val = res_val;
    while temp_val > 0
        invariant
            (forall |k: int| 0 <= k && k < result_vec.len() ==> (result_vec.index(k) == '0' || result_vec.index(k) == '1')),
        decreases temp_val
    {
        if temp_val % 2 == 1 {
            result_vec.insert(0, '1');
        } else {
            result_vec.insert(0, '0');
        }
        temp_val = temp_val / 2;
    }
    
    result_vec
}
// </vc-code>

fn main() {}
}
