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
/* helper modified by LLM (iteration 2): Fixed type suffixes and added additional lemmas */
proof fn exp_int_zero(x: nat)
    ensures Exp_int(x, 0) == 1
{
}

proof fn exp_int_rec(x: nat, y: nat)
    requires y > 0
    ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
}

proof fn str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn str2int_rec(s: Seq<char>, c: char)
    requires ValidBitString(s.push(c)),
    ensures Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1 } else { 0 })
{
}

proof fn mod_exp_property(x: nat, y: nat, z: nat)
    requires z > 1
    ensures Exp_int(x, y) % z == Exp_int(x % z, y) % z
{
}

proof fn nat_div_2_property(n: nat)
    ensures n >= 1 ==> n / 2 < n
{
}

proof fn mod_even_odd_property(a: nat, b: nat)
    requires b > 0
    ensures a % b == 0 || a % b == 1 when b == 2
{
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed nat type usage and compilation errors */
{
    let mut res = Vec::<char>::new();
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    let mut base = x_val % z_val;
    let mut exponent = y_val;
    let mut result = 1;
    
    while exponent > 0
        invariant
            result == Exp_int(base, exponent) % z_val,
            exponent >= 0,
        decreases exponent
    {
        if exponent % 2 == 1 {
            result = (result * base) % z_val;
        }
        base = (base * base) % z_val;
        exponent = exponent / 2;
    }
    
    let mut temp = result;
    while temp > 0
        invariant
            ValidBitString(res@),
            Str2Int(res@) == temp,
        decreases temp
    {
        if temp % 2 == 0 {
            res.push('0');
        } else {
            res.push('1');
        }
        temp = temp / 2;
    }
    
    res.reverse();
    if res.is_empty() {
        res.push('0');
    }
    
    res
}
// </vc-code>

fn main() {}
}
