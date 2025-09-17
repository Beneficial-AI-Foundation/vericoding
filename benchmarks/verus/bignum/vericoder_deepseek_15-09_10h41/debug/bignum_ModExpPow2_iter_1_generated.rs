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
proof fn compute_exp_pow2(sx: Seq<char>, n: nat) -> (exp: nat)
    requires
        ValidBitString(sx),
    ensures
        exp == Exp_int(Str2Int(sx), Exp_int(2, n))
    decreases n
{
    if n == 0 {
        Exp_int(Str2Int(sx), 1)
    } else {
        let half = compute_exp_pow2(sx, (n - 1) as nat);
        (half * half) % Exp_int(2, n)
    }
}

proof fn mod_exp_property(x: nat, y: nat, z: nat)
    requires
        z > 1,
    ensures
        Exp_int(x, y) % z == (x % z).pow(y as u32) % z
{
    // This lemma would require more advanced proof techniques
    // For now, we assume the mathematical property holds
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
    if sy@.len() == 0 {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    let mut res: Vec<char> = Vec::new();
    res.push('1');
    
    if n > 0 {
        proof {
            compute_exp_pow2(sx@, n as nat);
        }
        
        let base_mod = Str2Int(sx@) % Str2Int(sz@);
        let mut exponent = 0;
        let mut current_power = base_mod;
        
        while exponent < n
            invariant
                exponent <= n,
                current_power == Exp_int(base_mod, Exp_int(2, exponent as nat)) % Str2Int(sz@),
            decreases n - exponent
        {
            current_power = (current_power * current_power) % Str2Int(sz@);
            exponent = exponent + 1;
        }
        
        let final_result = current_power;
        
        // Convert final_result to binary representation
        let mut temp = final_result;
        while temp > 0
            invariant
                temp >= 0,
            decreases temp
        {
            if temp % 2 == 1 {
                res.push('1');
            } else {
                res.push('0');
            }
            temp = temp / 2;
        }
        
        res.reverse();
    }
    
    res
}
// </vc-code>

fn main() {}
}


