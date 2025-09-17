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

fn vec_from_nat(n: nat) -> Vec<char>
    ensures ValidBitString(result@), Str2Int(result@) == n
{
    /* helper modified by LLM (iteration 2): Helper function to convert nat to bit string Vec<char> */
    let mut result = Vec::new();
    let mut remaining = n;
    while remaining > 0
        invariant
            ValidBitString(result@),
            Str2Int(result@) + remaining * Exp_int(2, result@.len() as nat) == n
        decreases remaining
    {
        if remaining % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        remaining = remaining / 2;
    }
    result
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
    /* code modified by LLM (iteration 2): Fixed compilation errors with Vec<char> handling */
    let z_int = Str2Int(sz@);
    let mut x_int: nat = Str2Int(sx@);
    let mut y_int: nat = Str2Int(sy@);
    let mut result_int: nat = 1;
    
    proof {
        str2int_nonnegative(sy@);
        exp_int_nonnegative(Str2Int(sx@), y_int);
    }
    
    while y_int > 0
        invariant
            result_int == Exp_int(Str2Int(sx@), y_int) % z_int,
            0 <= y_int <= Str2Int(sy@)
        decreases y_int
    {
        if y_int % 2 == 1 {
            result_int = (result_int * x_int) % z_int;
        }
        
        x_int = (x_int * x_int) % z_int;
        y_int = y_int / 2;
        
        proof { mod_exp_lemmas(); }
    }
    
    vec_from_nat(result_int)
}
// </vc-code>

fn main() {}
}
