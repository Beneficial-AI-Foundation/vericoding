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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

spec fn AllZero(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0'
}

// <vc-helpers>
fn int_to_bitstring(n: nat, min_len: nat) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n,
        res@.len() >= min_len
{
    let mut result = Vec::new();
    let mut num = n;
    
    while num > 0
        invariant
            ValidBitString(result@)
    {
        if num % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        num = num / 2;
    }
    
    while result.len() < min_len
        invariant
            ValidBitString(result@)
    {
        result.push('0');
    }
    
    result.reverse();
    result
}

fn bitstring_mult_mod(a: &[char], b: &[char], m: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(a@),
        ValidBitString(b@),
        ValidBitString(m@),
        Str2Int(m@) > 1
    ensures
        ValidBitString(res@),
        Str2Int(res@) == (Str2Int(a@) * Str2Int(b@)) % Str2Int(m@)
{
    let product = Str2Int(a@) * Str2Int(b@);
    let modulus = Str2Int(m@);
    let result_val = product % modulus;
    int_to_bitstring(result_val, 1)
}
// </vc-helpers>

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
    if AllZero(sy@) {
        return int_to_bitstring(1, 1);
    }
    
    if sy@.len() == 1 && sy@[0] == '1' {
        let mod_val = Str2Int(sx@) % Str2Int(sz@);
        return int_to_bitstring(mod_val, 1);
    }
    
    let half_y = if sy@.len() > 1 {
        sy[0..sy.len()-1].to_vec()
    } else {
        vec!['0']
    };
    
    let temp_result = ModExp(sx, &half_y, sz);
    let squared = bitstring_mult_mod(&temp_result, &temp_result, sz);
    
    if sy@[sy@.len()-1] == '1' {
        bitstring_mult_mod(&squared, sx, sz)
    } else {
        squared
    }
}
// </vc-code>

fn main() {}
}


