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
spec fn nat_to_bin(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 { seq!['0'] } else { let rem = if n % 2 == 0 { '0' } else {'1'}; nat_to_bin(n / 2) + seq![rem] }
}

/* helper modified by LLM (iteration 3): kept previous implementation */
proof fn Str2Int_nat_to_bin(n: nat)
    ensures
        ValidBitString(nat_to_bin(n)),
        Str2Int(nat_to_bin(n)) == n,
    decreases n
{
    if n == 0 {
    } else {
        let rem = if n % 2 == 0 { '0' } else { '1' };
        Str2Int_nat_to_bin(n / 2);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed compilation error by removing 'int' type in exec code and using iterator over &[char] */
    let x: nat = Str2Int(sx@);
    let mod_val: nat = Str2Int(sz@);
    let mut base: nat = x % mod_val;
    let mut result: nat = 1;
    for &y_bit in sy.iter().rev() {
        if y_bit == '1' {
            result = (result * base) % mod_val;
        }
        base = (base * base) % mod_val;
    }
    let res_seq = nat_to_bin(result);
    return Vec::from_seq(res_seq);
}
// </vc-code>

fn main() {}
}
