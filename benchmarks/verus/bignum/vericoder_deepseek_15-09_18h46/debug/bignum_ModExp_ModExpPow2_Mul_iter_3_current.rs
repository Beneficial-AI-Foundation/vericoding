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

proof fn exp_int_monotonic(x: nat, y1: nat, y2: nat) 
    requires y1 <= y2, x >= 1 
    ensures Exp_int(x, y1) <= Exp_int(x, y2) 
{ 
    if y1 < y2 { 
        let y2_minus_1: nat = (y2 - 1) as nat; 
        exp_int_monotonic(x, y1, y2_minus_1); 
    } 
} 
proof fn str2int_nonnegative(s: Seq<char>) 
    requires ValidBitString(s) 
    ensures Str2Int(s) >= 0 
{ 
} 
proof fn str2int_monotonic(s1: Seq<char>, s2: Seq<char>) 
    requires ValidBitString(s1), ValidBitString(s2), s1.len() <= s2.len() 
    ensures Str2Int(s1) <= Str2Int(s2) 
{ 
} 
proof fn exp_int_property(x: nat, y: nat) 
    requires x >= 1 
    ensures Exp_int(x, y) >= 1 
{ 
} 
proof fn mod_exp_lemma(a: nat, b: nat, m: nat) 
    requires m > 1, b >= 1 
    ensures Exp_int(a, b) % m == (a * Exp_int(a, (b - 1) as nat)) % m 
{ 
}

// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fix nat/int usage in executable code */
    let x_val: u64 = Str2Int(sx@) as u64;
    let y_val: u64 = Str2Int(sy@) as u64;
    let z_val: u64 = Str2Int(sz@) as u64;
    let mut result: u64 = 1;
    let mut base: u64 = (x_val % z_val);
    let mut exp: u64 = y_val;
    
    while exp > 0
    {
        if exp % 2 == 1 {
            result = (result * base) % z_val;
        }
        base = (base * base) % z_val;
        exp = exp / 2;
    }
    
    let mut res_vec = Vec::new();
    let mut temp: u64 = result;
    
    while temp > 0
    {
        if temp % 2 == 1 {
            res_vec.push('1');
        } else {
            res_vec.push('0');
        }
        temp = temp / 2;
    }
    
    if res_vec.is_empty() {
        res_vec.push('0');
    }
    
    res_vec.reverse();
    res_vec
}
// </vc-code>

fn main() {}
}
