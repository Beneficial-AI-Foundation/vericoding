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
proof fn mod_exp_helper(x: nat, y: nat, z: nat) -> (r: nat)
    requires z > 1
    ensures r == Exp_int(x, y) % z
    decreases y
{
    if y == 0 {
        Exp_int(x, 0) % z
    } else {
        let half = mod_exp_helper(x, y - 1, z);
        (x * half) % z
    }
}

proof fn str2int_nonnegative(s: Seq<char>) 
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
{}

proof fn exp_positive_base(x: nat, y: nat) 
    ensures Exp_int(x, y) >= 1
{
}

proof fn mod_properties(a: int, b: int, m: int) 
    requires m > 1
    ensures (a * b) % m == (a % m) * (b % m) % m
{}

spec fn bitstring_len(s: Seq<char>) -> nat 
    requires ValidBitString(s)
{
    s.len() as nat
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let mut x_val = Str2Int(sx@);
    let mut y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    proof {
        str2int_nonnegative(sx@);
        str2int_nonnegative(sy@);
        str2int_nonnegative(sz@);
        exp_positive_base(x_val, y_val);
    }
    
    let mut result_val = mod_exp_helper(x_val, y_val, z_val);
    
    proof {
        assert(result_val == Exp_int(x_val, y_val) % z_val);
    }
    
    // Convert result_val to binary representation
    let mut val = result_val;
    let mut bits = Vec::<char>::new();
    
    while val > 0
        invariant
            ValidBitString(bits@),
            Str2Int(bits@) == val,
        decreases val
    {
        let bit = if val % 2 == 0 { '0' } else { '1' };
        bits.push(bit);
        val = val / 2;
    }
    
    bits.reverse();
    
    if bits.is_empty() {
        bits.push('0');
    }
    
    bits
}
// </vc-code>

fn main() {}
}
