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
        assert(Exp_int(x, 0) == 1) by {
            assert(Exp_int(x, 0) == 1);
        };
        1nat % z
    } else {
        let half = mod_exp_helper(x, (y - 1) as nat, z);
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
    if y > 0 {
        exp_positive_base(x, (y - 1) as nat);
    }
}

proof fn mod_properties(a: nat, b: nat, m: nat) 
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
/* code modified by LLM (iteration 4): fix nat to int conversion error */
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    proof {
        str2int_nonnegative(sx@);
        str2int_nonnegative(sy@);
        str2int_nonnegative(sz@);
        exp_positive_base(x_val, y_val);
    }
    
    let result_val = mod_exp_helper(x_val, y_val, z_val);
    
    proof {
        assert(result_val == Exp_int(x_val, y_val) % z_val);
    }
    
    // Convert result_val to binary representation
    ghost {
        let val: nat = result_val;
        let ghost mut bits_seq = Seq::<char>::empty();
        let ghost mut temp_val = val;
        
        while temp_val > 0
            invariant
                ValidBitString(bits_seq),
                Str2Int(bits_seq) == temp_val,
                temp_val >= 0,
            decreases temp_val
        {
            let rem = temp_val % 2;
            let bit = if rem == 0 { '0' } else { '1' };
            bits_seq = bits_seq.push(bit);
            temp_val = temp_val / 2;
        }
        
        bits_seq = bits_seq.reverse();
        
        if bits_seq.len() == 0 {
            bits_seq = bits_seq.push('0');
        }
    }
    
    let result_vec = Vec::<char>::from_seq(bits_seq);
    result_vec
}
// </vc-code>

fn main() {}
}
