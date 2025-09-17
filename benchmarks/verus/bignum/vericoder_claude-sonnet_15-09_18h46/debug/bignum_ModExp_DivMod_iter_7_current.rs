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
/* helper modified by LLM (iteration 7): fixed nat literal syntax errors by using proper numeric literals */
exec fn char_to_digit(c: char) -> (result: nat)
    requires c == '0' || c == '1'
    ensures result == 0 || result == 1,
        result == (if c == '1' { 1 } else { 0 })
{
    if c == '1' { 1 } else { 0 }
}

exec fn digit_to_char(d: nat) -> (result: char)
    requires d == 0 || d == 1
    ensures result == '0' || result == '1',
        result == (if d == 1 { '1' } else { '0' })
{
    if d == 1 { '1' } else { '0' }
}

exec fn add_binary(a: &[char], b: &[char]) -> (result: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@)
    ensures ValidBitString(result@)
{
    let mut res = Vec::new();
    let mut carry = 0;
    let mut i = 0;
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    
    while i < max_len || carry > 0
        invariant ValidBitString(res@), carry <= 1
    {
        let digit_a = if i < a.len() { char_to_digit(a[a.len() - 1 - i]) } else { 0 };
        let digit_b = if i < b.len() { char_to_digit(b[b.len() - 1 - i]) } else { 0 };
        let sum = digit_a + digit_b + carry;
        res.push(digit_to_char(sum % 2));
        carry = sum / 2;
        i += 1;
    }
    
    res.reverse();
    if res.len() == 0 {
        res.push('0');
    }
    res
}

exec fn multiply_by_two(s: &[char]) -> (result: Vec<char>)
    requires ValidBitString(s@)
    ensures ValidBitString(result@)
{
    let mut res = Vec::from(s);
    res.push('0');
    res
}

exec fn modulo_binary(a: &[char], m: &[char]) -> (result: Vec<char>)
    requires ValidBitString(a@), ValidBitString(m@), m@.len() > 0, Str2Int(m@) > 1
    ensures ValidBitString(result@)
{
    let mut res = Vec::from(a);
    while res.len() >= m.len() && !(res.len() == 1 && res[0] == '0')
        invariant ValidBitString(res@)
    {
        let m_vec = Vec::from(m);
        if res.len() > m_vec.len() || (res.len() == m_vec.len() && res >= m_vec) {
            let mut temp = Vec::new();
            let mut borrow = 0;
            let mut i = 0;
            while i < res.len()
                invariant ValidBitString(temp@)
            {
                let pos = res.len() - 1 - i;
                let digit_res = char_to_digit(res[pos]);
                let digit_m = if i < m.len() { char_to_digit(m[m.len() - 1 - i]) } else { 0 };
                
                if digit_res >= digit_m + borrow {
                    temp.push(digit_to_char(digit_res - digit_m - borrow));
                    borrow = 0;
                } else {
                    temp.push(digit_to_char(digit_res + 2 - digit_m - borrow));
                    borrow = 1;
                }
                i += 1;
            }
            temp.reverse();
            while temp.len() > 1 && temp[0] == '0' {
                temp.remove(0);
            }
            res = temp;
        } else {
            break;
        }
    }
    res
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 7): fixed nat literal syntax errors by using proper numeric literals */
    if sy.len() == 0 {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    if sy.len() == 1 && sy[0] == '0' {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    let mut base = Vec::from(sx);
    let mut exp = Vec::from(sy);
    let modulus = sz;
    let mut result = Vec::new();
    result.push('1');
    
    while exp.len() > 0 && !(exp.len() == 1 && exp[0] == '0')
        invariant ValidBitString(base@),
            ValidBitString(exp@),
            ValidBitString(result@)
    {
        if exp[exp.len() - 1] == '1' {
            let temp_result = multiply_by_two(&result);
            result = modulo_binary(&temp_result, modulus);
        }
        
        let temp_base = multiply_by_two(&base);
        base = modulo_binary(&temp_base, modulus);
        
        let mut new_exp = Vec::new();
        let mut carry = 0;
        let mut i = 0;
        while i < exp.len()
            invariant ValidBitString(new_exp@)
        {
            let digit = char_to_digit(exp[i]) + carry * 2;
            new_exp.push(digit_to_char(digit / 2));
            carry = digit % 2;
            i += 1;
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
