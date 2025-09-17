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
fn reverse_bits(s: Vec<char>) -> Vec<char> {
    let mut result = Vec::new();
    let mut i = s.len();
    while i > 0 {
        i = i - 1;
        result.push(s[i]);
    }
    result
}

proof fn str2int_recursive_proof(s: Seq<char>, i: int)
    requires
        ValidBitString(s),
        0 <= i && i <= s.len() as int,
    ensures
        Str2Int(s.subrange(0, i)) == Str2Int(s.subrange(0, i)),
    decreases s.len() as int - i
{
    if i > 0 {
        str2int_recursive_proof(s, i - 1);
    }
}

proof fn exp_int_recursive_proof(x: nat, y: nat)
    ensures
        Exp_int(x, y) == Exp_int(x, y),
    decreases y
{
    if y > 0 {
        exp_int_recursive_proof(x, (y - 1) as nat);
    }
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut carry = 0;
    let mut i = s1.len() as int - 1;
    let mut j = s2.len() as int - 1;
    
    while i >= 0 || j >= 0 || carry > 0 {
        let bit1 = if i >= 0 { if s1[i as usize] == '1' { 1 } else { 0 } } else { 0 };
        let bit2 = if j >= 0 { if s2[j as usize] == '1' { 1 } else { 0 } } else { 0 };
        let sum = bit1 + bit2 + carry;
        
        if sum % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        carry = sum / 2;
        
        i = i - 1;
        j = j - 1;
    }
    
    let reversed = reverse_bits(result);
    reversed
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
{
    let mut result = Vec::new();
    let mut temp = Vec::new();
    temp.push('0');
    
    let mut i = s2.len() as int - 1;
    while i >= 0 {
        if s2[i as usize] == '1' {
            let mut sum = Vec::new();
            let mut carry = 0;
            let mut j = s1.len() as int - 1;
            let mut k = temp.len() as int - 1;
            
            while j >= 0 || k >= 0 || carry > 0 {
                let bit1 = if j >= 0 { if s1[j as usize] == '1' { 1 } else { 0 } } else { 0 };
                let bit2 = if k >= 0 { if temp[k as usize] == '1' { 1 } else { 0 } } else { 0 };
                let total = bit1 + bit2 + carry;
                
                if total % 2 == 1 {
                    sum.push('1');
                } else {
                    sum.push('0');
                }
                carry = total / 2;
                
                j = j - 1;
                k = k - 1;
            }
            
            temp = reverse_bits(sum);
        }
        
        if i > 0 {
            temp.push('0');
        }
        
        i = i - 1;
    }
    
    result = temp;
    result
}
// </vc-code>

fn main() {}
}


