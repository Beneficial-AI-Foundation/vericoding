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
/* helper modified by LLM (iteration 4): moved helper function to helpers section */
exec fn reverse_vec<T>(v: &mut Vec<T>)
    ensures v@ == old(v)@.reverse()
{
    let len = v.len();
    let mut i = 0;
    while i < len / 2
        invariant
            i <= len / 2,
            v@.len() == len
    {
        let temp = v[i];
        v.set(i, v[len - 1 - i]);
        v.set(len - 1 - i, temp);
        i = i + 1;
    }
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
    /* code modified by LLM (iteration 4): fixed Add function implementation */
    let mut result = Vec::<char>::new();
    let mut carry = 0;
    let mut i1 = s1.len();
    let mut i2 = s2.len();
    
    while i1 > 0 || i2 > 0 || carry > 0
        invariant
            ValidBitString(result@),
            carry <= 2,
            i1 <= s1.len(),
            i2 <= s2.len()
    {
        let bit1 = if i1 > 0 { if s1[i1 - 1] == '1' { 1 } else { 0 } } else { 0 };
        let bit2 = if i2 > 0 { if s2[i2 - 1] == '1' { 1 } else { 0 } } else { 0 };
        let sum = bit1 + bit2 + carry;
        
        if sum % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        
        carry = sum / 2;
        
        if i1 > 0 { i1 = i1 - 1; }
        if i2 > 0 { i2 = i2 - 1; }
    }
    
    let len = result.len();
    let mut i = 0;
    while i < len / 2
        invariant
            i <= len / 2,
            result@.len() == len
    {
        let temp = result[i];
        result.set(i, result[len - 1 - i]);
        result.set(len - 1 - i, temp);
        i = i + 1;
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    result
}
// </vc-code>

fn main() {}
}


