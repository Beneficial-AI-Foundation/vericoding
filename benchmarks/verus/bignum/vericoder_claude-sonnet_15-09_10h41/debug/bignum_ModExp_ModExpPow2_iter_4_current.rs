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
/* helper modified by LLM (iteration 4): fixed type mismatches with nat literals */
exec fn char_to_digit(c: char) -> (result: nat)
    requires c == '0' || c == '1'
    ensures result == 0 || result == 1,
        c == '0' ==> result == 0,
        c == '1' ==> result == 1
{
    if c == '1' { 1nat } else { 0nat }
}

exec fn digit_to_char(d: nat) -> (result: char)
    requires d == 0 || d == 1
    ensures result == '0' || result == '1',
        d == 0 ==> result == '0',
        d == 1 ==> result == '1'
{
    if d == 1nat { '1' } else { '0' }
}

exec fn add_binary_strings(a: &[char], b: &[char]) -> (result: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@)
    ensures ValidBitString(result@)
{
    let mut res = Vec::new();
    let mut carry = 0nat;
    let mut i = a.len();
    let mut j = b.len();
    
    while i > 0 || j > 0 || carry > 0
        invariant ValidBitString(res@)
    {
        let mut sum = carry;
        if i > 0 {
            i = i - 1;
            sum = sum + char_to_digit(a[i]);
        }
        if j > 0 {
            j = j - 1;
            sum = sum + char_to_digit(b[j]);
        }
        res.insert(0, digit_to_char(sum % 2nat));
        carry = sum / 2nat;
    }
    
    if res.len() == 0 {
        res.push('0');
    }
    
    res
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed type mismatches with nat literals */
    if sy.len() == 1 && sy[0] == '0' {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    if sx.len() == 1 && sx[0] == '0' {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    if sx.len() == 1 && sx[0] == '1' {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    let mut result = Vec::new();
    result.push('1');
    let mut exp = Vec::from(sy);
    let mut base = Vec::from(sx);
    
    while exp.len() > 0 && !(exp.len() == 1 && exp[0] == '0')
        invariant ValidBitString(result@), ValidBitString(exp@), ValidBitString(base@)
    {
        if exp[exp.len() - 1] == '1' {
            result = add_binary_strings(&result, &base);
        }
        
        if exp.len() == 1 && exp[0] == '1' {
            break;
        }
        
        base = add_binary_strings(&base, &base);
        
        let mut new_exp = Vec::new();
        let mut carry = 0nat;
        for i in 0..exp.len() {
            let digit = char_to_digit(exp[i]) + carry * 2nat;
            new_exp.push(digit_to_char(digit / 2nat));
            carry = digit % 2nat;
        }
        
        while new_exp.len() > 1 && new_exp[0] == '0' {
            new_exp.remove(0);
        }
        
        exp = new_exp;
    }
    
    result
}
// </vc-code>

fn main() {}
}
