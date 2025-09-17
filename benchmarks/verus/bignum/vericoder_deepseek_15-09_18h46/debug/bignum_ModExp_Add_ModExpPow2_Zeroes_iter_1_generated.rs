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

proof fn exp_int_zero_base(x: nat)
    ensures Exp_int(0, x) == (if x == 0 { 1 } else { 0 })
{
    if x > 0 {
        exp_int_zero_base((x - 1) as nat);
    }
}

proof fn exp_int_one_exponent(x: nat)
    ensures Exp_int(x, 1) == x
{
}

proof fn exp_int_product_rule(x: nat, y: nat, z: nat)
    ensures Exp_int(x, y + z) == Exp_int(x, y) * Exp_int(x, z)
{
    if z > 0 {
        exp_int_product_rule(x, y, (z - 1) as nat);
    }
}

proof fn str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn str2int_single_char(c: char)
    requires c == '0' || c == '1'
    ensures Str2Int(Seq::new(1, |i: int| c)) == (if c == '1' { 1 } else { 0 })
{
}

proof fn str2int_append_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s + Seq::new(1, |i: int| '0')) == 2 * Str2Int(s)
{
    if s.len() > 0 {
        str2int_append_zero(s.subrange(0, s.len() as int - 1));
    }
}

proof fn str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s + Seq::new(1, |i: int| '1')) == 2 * Str2Int(s) + 1
{
    if s.len() > 0 {
        str2int_append_one(s.subrange(0, s.len() as int - 1));
    }
}

proof fn mod_exp_property(x: nat, y: nat, z: nat)
    requires z > 1
    ensures Exp_int(x, y) % z == (x % z).pow(y as u32) % z
{
    if y > 0 {
        mod_exp_property(x, (y - 1) as nat, z);
    }
}

// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    proof {
        mod_exp_property(x_val, y_val, z_val);
    }
    
    let mod_result = (x_val % z_val).pow(y_val as u32) % z_val;
    
    let mut temp = mod_result;
    while temp > 0
        invariant
            temp >= 0,
            ValidBitString(result@),
            Str2Int(result@) == mod_result
        decreases temp
    {
        if temp % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        temp = temp / 2;
    }
    
    if result.is_empty() {
        result.push('0');
    }
    
    result.reverse();
    result
}
// </vc-code>

fn main() {}
}
