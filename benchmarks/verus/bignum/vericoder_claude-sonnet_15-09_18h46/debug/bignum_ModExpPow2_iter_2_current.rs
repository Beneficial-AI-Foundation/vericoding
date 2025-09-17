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
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed type annotations and nat operations */
spec fn pow_mod(base: nat, exp: nat, modulus: nat) -> nat
    requires modulus > 0
    decreases exp
{
    if exp == 0 {
        1nat % modulus
    } else if exp % 2nat == 0nat {
        let half_pow = pow_mod(base, exp / 2nat, modulus);
        (half_pow * half_pow) % modulus
    } else {
        (base * pow_mod(base, exp - 1nat, modulus)) % modulus
    }
}

exec fn nat_to_bit_string(mut n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@),
        Str2Int(res@) == n
{
    if n == 0nat {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    let mut result = Vec::new();
    let mut temp = n;
    
    while temp > 0nat
        invariant ValidBitString(result@)
    {
        if temp % 2nat == 0nat {
            result.push('0');
        } else {
            result.push('1');
        }
        temp = temp / 2nat;
    }
    
    result.reverse();
    result
}
// </vc-helpers>

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
    /* code modified by LLM (iteration 2): fixed type annotations for nat/int operations */
    if n == 0int {
        return nat_to_bit_string(1nat % Str2Int(sz@));
    }
    
    let base_val = Str2Int(sx@);
    let exp_val = Str2Int(sy@);
    let mod_val = Str2Int(sz@);
    
    if exp_val == 0nat {
        return nat_to_bit_string(1nat % mod_val);
    }
    
    if exp_val == 1nat {
        return nat_to_bit_string(base_val % mod_val);
    }
    
    let half_exp = exp_val / 2nat;
    let half_exp_bits = nat_to_bit_string(half_exp);
    
    let half_result = ModExpPow2(sx, &half_exp_bits, (n - 1int), sz);
    let half_val = Str2Int(half_result@);
    
    let squared = (half_val * half_val) % mod_val;
    
    if exp_val % 2nat == 0nat {
        nat_to_bit_string(squared)
    } else {
        nat_to_bit_string((base_val * squared) % mod_val)
    }
}
// </vc-code>

fn main() {}
}


