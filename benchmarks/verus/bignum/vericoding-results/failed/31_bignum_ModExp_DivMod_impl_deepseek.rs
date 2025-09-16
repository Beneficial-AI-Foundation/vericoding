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
/* helper modified by LLM (iteration 10): Remove vec_from_nat helper and use proper nat arithmetic without literal suffixes */
fn nat_from_str(s: Seq<char>) -> (res: nat)
    requires ValidBitString(s)
    ensures res == Str2Int(s)
{
    if s.len() == 0 {
        0
    } else {
        let rest = nat_from_str(s.subrange(0, s.len() as int - 1));
        if s.index(s.len() as int - 1) == '1' {
            2 * rest + 1
        } else {
            2 * rest
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed nat type conversion errors using proper nat arithmetic */
{
    let x_int = nat_from_str(sx@);
    let y_int = nat_from_str(sy@);
    let z_int = nat_from_str(sz@);
    let mut base = x_int % z_int;
    let mut exponent = y_int;
    let mut result = 1;
    
    while exponent > 0
        invariant
            result * Exp_int(base, exponent) % z_int == Exp_int(x_int, y_int) % z_int,
            0 <= exponent && exponent <= y_int
        decreases exponent
    {
        if exponent % 2 == 1 {
            result = (result * base) % z_int;
        }
        
        base = (base * base) % z_int;
        exponent = exponent / 2;
    }
    
    let mut temp = result;
    let mut chars = Vec::new();
    
    while temp > 0
        invariant
            ValidBitString(chars@),
            Str2Int(chars@) == temp
        decreases temp
    {
        if temp % 2 == 1 {
            chars.push('1');
        } else {
            chars.push('0');
        }
        temp = temp / 2;
    }
    
    if chars.is_empty() {
        chars.push('0');
    }
    
    chars.reverse();
    chars
}
// </vc-code>

fn main() {}
}
