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

proof fn exp_int_nonnegative(x: nat, y: nat) 
    ensures Exp_int(x, y) >= 0
    decreases y
{
    if y > 0 {
        exp_int_nonnegative(x, (y - 1) as nat);
    }
}

proof fn str2int_nonnegative(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
    decreases s.len()
{
    if s.len() > 0 {
        str2int_nonnegative(s.subrange(0, s.len() as int - 1));
    }
}

proof fn exp_int_monotonic(x: nat, y: nat, z: nat)
    requires y <= z
    ensures Exp_int(x, y) <= Exp_int(x, z)
    decreases z - y
{
    if y < z {
        exp_int_monotonic(x, y, (z - 1) as nat);
    }
}

proof fn mod_exp_lemmas()
{
    // Modular arithmetic properties
}

// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let mut x = *sx;
    let mut y = *sy;
    let z_int = Str2Int(sz@);
    let mut result_int: nat = 1;
    
    proof {
        str2int_nonnegative(y@);
        exp_int_nonnegative(Str2Int(x@), Str2Int(y@));
    }
    
    while y.len() > 0
        invariant
            ValidBitString(x@),
            ValidBitString(y@),
            ValidBitString(Vec::from_seq(result_int))@,
            result_int == Exp_int(Str2Int(sx@), Str2Int(sy@) - Str2Int(y@)) % z_int,
        decreases y@.len()
    {
        if y[y.len() - 1] == '1' {
            result_int = (result_int * Str2Int(x@)) % z_int;
        }
        
        // Square x
        x = Vec::from_seq(Exp_int(Str2Int(x@), 2) % z_int);
        proof { mod_exp_lemmas(); }
        
        // Right-shift y
        let new_len = y.len() - 1;
        let mut new_y = Vec::new();
        for i in 0..new_len {
            new_y.push(y[i]);
        }
        y = Vec::from_seq(new_y@);
    }
    
    Vec::from_seq(result_int)
}
// </vc-code>

fn main() {}
}
