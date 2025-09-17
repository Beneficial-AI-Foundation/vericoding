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
/* helper modified by LLM (iteration 4): kept previous implementation */
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
    /* code modified by LLM (iteration 4): fixed type error for nat literal, used manual loop instead of iterator for rev, and built Vec<char> manually */
    let x: nat = Str2Int(sx@);
    let mod_val: nat = Str2Int(sz@);
    let mut base: nat = x % mod_val;
    let mut result: nat = 1nat;
    let sy_seq = sy@;
    let mut i = sy_seq.len() as int - 1;
    while i >= 0
    {
        let y_bit = sy_seq[i];
        if y_bit == '1' {
            result = (result * base) % mod_val;
        }
        base = (base * base) % mod_val;
        i -= 1;
    }
    let res_seq = nat_to_bin(result);
    let mut res_vec: Vec<char> = Vec::new();
    let mut j: int = 0;
    while j < res_seq.len() as int
    {
        res_vec.push(res_seq[j]);
        j += 1;
    }
    return res_vec;
}
// </vc-code>

fn main() {}
}
