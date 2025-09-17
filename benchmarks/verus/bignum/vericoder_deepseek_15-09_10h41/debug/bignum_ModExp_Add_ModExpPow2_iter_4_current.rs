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
/* helper modified by LLM (iteration 4): Fixed type annotation error in str2int_rec and added proper nat to usize conversion helpers */
proof fn str2int_rec(s: Seq<char>, c: char)
    requires ValidBitString(s.push(c)),
    ensures Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat })
{
}

proof fn nat_to_usize(n: nat) -> (r: usize)
    ensures r == n as usize
{
}

proof fn usize_to_nat(n: usize) -> (r: nat)
    ensures r == n as nat
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
/* code modified by LLM (iteration 4): Fixed cast errors and properly converted between nat and usize types */
{
    let mut res = Vec::<char>::new();
    let x_val: nat = Str2Int(sx@);
    let y_val: nat = Str2Int(sy@);
    let z_val: nat = Str2Int(sz@);
    
    let mut x_usize = x_val as usize;
    let mut y_usize = y_val as usize;
    let mut z_usize = z_val as usize;
    
    let mut base = x_usize % z_usize;
    let mut exponent = y_usize;
    let mut result = 1;
    
    while exponent > 0
        invariant
            result as nat == Exp_int(base as nat, exponent as nat) % z_val,
            exponent >= 0,
        decreases exponent
    {
        if exponent % 2 == 1 {
            result = (result * base) % z_usize;
        }
        base = (base * base) % z_usize;
        exponent = exponent / 2;
    }
    
    let mut temp = result;
    while temp > 0
        invariant
            ValidBitString(res@),
            Str2Int(res@) == temp as nat,
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
