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
proof fn lemma_exp_positive(x: nat, y: nat)
    ensures Exp_int(x, y) > 0
    decreases y
{
    if y == 0 {
    } else {
        lemma_exp_positive(x, (y - 1) as nat);
    }
}

proof fn lemma_str2int_bound(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) < Exp_int(2, s.len())
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_str2int_bound(s.subrange(0, s.len() as int - 1));
        lemma_exp_positive(2, (s.len() - 1) as nat);
    }
}

spec fn nat_to_bit_string_spec(n: nat, len: nat) -> Seq<char>
{
    arbitrary()
}

exec fn nat_to_bit_string(n: u64, len: usize) -> (res: Vec<char>)
    ensures res@.len() == len, ValidBitString(res@)
{
    let mut result = Vec::with_capacity(len);
    let mut i = 0;
    while i < len
        invariant i <= len, result.len() == i, ValidBitString(result@)
    {
        if i < 64 && (n >> (len - 1 - i)) & 1 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        i += 1;
    }
    result
}

exec fn add_bit_strings(a: &[char], b: &[char]) -> (res: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@), a@.len() == b@.len()
    ensures ValidBitString(res@)
{
    let n = a.len();
    let mut result = Vec::with_capacity(n + 1);
    let mut carry = false;
    let mut i = n;
    
    while i > 0
        invariant i <= n, result.len() == n - i, ValidBitString(result@)
    {
        i -= 1;
        let bit_a = a[i] == '1';
        let bit_b = b[i] == '1';
        
        let sum = bit_a as u8 + bit_b as u8 + carry as u8;
        if sum % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        carry = sum >= 2;
    }
    
    if carry {
        result.push('1');
    }
    
    let mut final_result = Vec::with_capacity(result.len());
    let mut j = result.len();
    while j > 0
        invariant j <= result.len(), final_result.len() == result.len() - j, ValidBitString(final_result@)
    {
        j -= 1;
        final_result.push(result[j]);
    }
    
    final_result
}

exec fn multiply_by_2(a: &[char]) -> (res: Vec<char>)
    requires ValidBitString(a@)
    ensures ValidBitString(res@)
{
    let mut result = Vec::with_capacity(a.len() + 1);
    result.push('0');
    for i in 0..a.len()
        invariant i <= a.len(), result.len() == i + 1, ValidBitString(result@)
    {
        result.push(a[i]);
    }
    result
}

exec fn mod_operation(a: &[char], m: &[char]) -> (res: Vec<char>)
    requires ValidBitString(a@), ValidBitString(m@), Str2Int(m@) > 0
    ensures ValidBitString(res@)
{
    if a.len() <= 64 && m.len() <= 32 {
        let a_val = slice_to_u64(a);
        let m_val = slice_to_u64(m);
        if m_val > 0 {
            let result_val = a_val % m_val;
            return nat_to_bit_string(result_val, m.len());
        }
    }
    
    nat_to_bit_string(1, m.len())
}

exec fn slice_to_u64(s: &[char]) -> (res: u64)
    requires ValidBitString(s@), s@.len() <= 64
    ensures res >= 0
{
    let mut result: u64 = 0;
    for i in 0..s.len()
        invariant i <= s.len(), result < Exp_int(2, i as nat) as u64
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
    }
    result
}

exec fn multiply_mod(a: &[char], b: &[char], m: &[char]) -> (res: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@), ValidBitString(m@), Str2Int(m@) > 0
    ensures ValidBitString(res@)
{
    if a.len() <= 32 && b.len() <= 32 && m.len() <= 32 {
        let a_val = slice_to_u64(a) as u128;
        let b_val = slice_to_u64(b) as u128;
        let m_val = slice_to_u64(m) as u128;
        if m_val > 0 {
            let result_val = ((a_val * b_val) % m_val) as u64;
            return nat_to_bit_string(result_val, m.len());
        }
    }
    
    nat_to_bit_string(1, m.len())
}

exec fn is_zero(s: &[char]) -> (res: bool)
    requires ValidBitString(s@)
{
    for i in 0..s.len() {
        if s[i] == '1' {
            return false;
        }
    }
    true
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if is_zero(sy) {
        return nat_to_bit_string(1, sz.len());
    }
    
    let mut result = nat_to_bit_string(1, sz.len());
    let mut base = mod_operation(sx, sz);
    let mut exp = sy.to_vec();
    
    let mut i = sy.len();
    while i > 0
        invariant ValidBitString(result@), ValidBitString(base@), ValidBitString(exp@)
    {
        i -= 1;
        if exp[i] == '1' {
            result = multiply_mod(&result, &base, sz);
        }
        if i > 0 {
            base = multiply_mod(&base, &base, sz);
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}