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
/* helper modified by LLM (iteration 4): Fix type conversion helpers */
spec fn to_nat(n: int) -> nat
    requires
        n >= 0
    ensures
        to_nat(n) == n as nat
{
    n as nat
}

proof fn exp_int_property(x: nat, y: nat, z: nat)
    requires
        z > 1,
    ensures
        Exp_int(x, y) % z == Exp_int(x % z, y) % z
{
    // This property will be used for modular exponentiation
}

proof fn exp_int_pow2_property(n: nat) -> (result: nat)
    requires
        n >= 0,
    ensures
        result == Exp_int(2, n)
    decreases n
{
    if n == 0 {
        1
    } else {
        let half = exp_int_pow2_property((n - 1) as nat);
        half * 2
    }
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
    /* code modified by LLM (iteration 4): Fix nat/int type conversion issues */
    let sy_nat: nat = Str2Int(sy@);
    let sz_nat: nat = Str2Int(sz@);
    
    if sy_nat == 0nat {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    let mut res: Vec<char> = Vec::new();
    res.push('1');
    
    if n > 0 {
        proof {
            exp_int_pow2_property(to_nat(n));
            exp_int_property(Str2Int(sx@), sy_nat, sz_nat);
        }
        
        let base_mod = Str2Int(sx@) % sz_nat;
        let mut exponent: int = 0;
        let mut current_power: nat = base_mod;
        
        while exponent < n
            invariant
                exponent <= n,
                current_power == Exp_int(base_mod, Exp_int(2, to_nat(exponent))) % sz_nat,
            decreases n - exponent
        {
            current_power = (current_power * current_power) % sz_nat;
            exponent = exponent + 1;
        }
        
        let final_result = current_power;
        
        // Convert final_result to binary representation
        let mut temp: nat = final_result;
        while temp > 0nat
            invariant
                temp >= 0,
            decreases temp
        {
            if temp % 2nat == 1nat {
                res.push('1');
            } else {
                res.push('0');
            }
            temp = temp / 2nat;
        }
        
        res.reverse();
    }
    
    res
}
// </vc-code>

fn main() {}
}


