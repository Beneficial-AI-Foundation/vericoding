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
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* helper modified by LLM (iteration 3): added binary_add helper for addition */
fn binary_add(a: &[char], b: &[char]) -> Vec<char> {
    let mut result = Vec::new();
    let mut carry = 0;
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    
    let mut i = 0;
    while i < max_len || carry > 0 {
        let a_bit = if i < a.len() { if a[a.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let b_bit = if i < b.len() { if b[b.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let sum = a_bit + b_bit + carry;
        result.push(if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
        i += 1;
    }
    
    result.reverse();
    result
}

/* helper modified by LLM (iteration 3): added binary_mod helper for modulo */
fn binary_mod(a: &[char], m: &[char]) -> Vec<char> {
    if a.len() < m.len() || (a.len() == m.len() && compare_binary(a, m) < 0) {
        return a.to_vec();
    }
    
    let mut remainder = a.to_vec();
    while remainder.len() > m.len() || (remainder.len() == m.len() && compare_binary(&remainder, m) >= 0) {
        remainder = binary_subtract(&remainder, m);
    }
    remainder
}

/* helper modified by LLM (iteration 3): added binary comparison helper */
fn compare_binary(a: &[char], b: &[char]) -> i32 {
    if a.len() != b.len() {
        return if a.len() > b.len() { 1 } else { -1 };
    }
    
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return if a[i] == '1' { 1 } else { -1 };
        }
        i += 1;
    }
    0
}

/* helper modified by LLM (iteration 3): added binary subtraction helper */
fn binary_subtract(a: &[char], b: &[char]) -> Vec<char> {
    let mut result = Vec::new();
    let mut borrow = 0;
    
    let mut i = 0;
    while i < a.len() {
        let a_bit = if a[a.len() - 1 - i] == '1' { 1 } else { 0 };
        let b_bit = if i < b.len() { if b[b.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        
        let diff = a_bit - b_bit - borrow;
        if diff < 0 {
            result.push('1');
            borrow = 1;
        } else {
            result.push(if diff == 1 { '1' } else { '0' });
            borrow = 0;
        }
        i += 1;
    }
    
    result.reverse();
    while result.len() > 1 && result[0] == '0' {
        result.remove(0);
    }
    result
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
    /* code modified by LLM (iteration 3): using helper functions for binary operations */
    if s1.len() == 0 || s2.len() == 0 {
        return vec!['0'];
    }
    
    let mut result = vec!['0'];
    let mut i = 0;
    
    while i < s2.len()
        invariant
            i <= s2.len(),
            ValidBitString(result@),
            ValidBitString(s1@),
            ValidBitString(s2@)
    {
        if s2[i] == '1' {
            let shift_amount = s2.len() - 1 - i;
            let mut shifted_s1 = s1.to_vec();
            let mut j = 0;
            while j < shift_amount
                invariant
                    j <= shift_amount,
                    ValidBitString(shifted_s1@)
            {
                shifted_s1.push('0');
                j += 1;
            }
            result = binary_add(&result, &shifted_s1);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}


