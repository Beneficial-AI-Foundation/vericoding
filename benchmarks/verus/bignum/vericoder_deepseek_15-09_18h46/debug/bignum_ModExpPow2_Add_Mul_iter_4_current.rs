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
/* helper modified by LLM (iteration 4): Add proper Mod function spec with curly braces */
spec fn Mod(val: nat, modulus: nat) -> nat {
    val % modulus
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fix compilation and verification errors in Add function */
    let mut carry: int = 0;
    let mut i = s1.len() as int - 1;
    let mut j = s2.len() as int - 1;
    let mut result = Vec::<char>::new();
    
    while i >= 0 || j >= 0 || carry > 0
        invariant
            0 <= result.len(),
            carry == 0 || carry == 1,
            ValidBitString(result@),
            Str2Int(result@) + Exp_int(2, result.len() as nat) * carry == 
                Str2Int(s1@.subrange(i + 1, s1.len() as int)) + 
                Str2Int(s2@.subrange(j + 1, s2.len() as int))
        decreases (if i >= 0 { i } else { 0 }) + (if j >= 0 { j } else { 0 }) + carry + 1
    {
        let bit1 = if i >= 0 { if s1[i as usize] == '1' { 1 } else { 0 } } else { 0 };
        let bit2 = if j >= 0 { if s2[j as usize] == '1' { 1 } else { 0 } } else { 0 };
        let sum = bit1 + bit2 + carry;
        result.push(if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
        if i >= 0 { i -= 1; }
        if j >= 0 { j -= 1; }
    }
    result.reverse();
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
    /* code modified by LLM (iteration 4): Fix compilation and verification errors in ModExpPow2 */
    if n <= 0 {
        let mut result = Vec::<char>::new();
        if sy[0] == '1' {
            result.push('1');
        } else {
            result.push('0');
        }
        result
    } else {
        let half_n = n - 1;
        let half_sy = &sy[0..sy.len() - 1];
        let half_result = ModExpPow2(sx, half_sy, half_n, sz);
        let squared = Mul(&half_result, &half_result);
        let mut mod_result = ModExpPow2(&squared, &Vec::from_vec(vec!['1']), 0, sz);
        if sy[sy.len() - 1] == '1' {
            let temp = Mul(&mod_result, sx);
            mod_result = ModExpPow2(&temp, &Vec::from_vec(vec!['1']), 0, sz);
        }
        mod_result
    }
}
// </vc-code>

fn main() {}
}
