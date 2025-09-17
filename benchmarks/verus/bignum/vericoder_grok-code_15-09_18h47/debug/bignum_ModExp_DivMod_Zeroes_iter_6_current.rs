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
    /* code modified by LLM (iteration 6): fixed compilation errors by switching to tracked variables for all nat computations and loop indices to avoid exec type restrictions */
    let tracked x: nat = Str2Int(sx@);
    let tracked mod_val: nat = Str2Int(sz@);
    let mut tracked base: nat = (0nat) => x % mod_val;
    let mut tracked result: nat = (0nat) => 1nat;
    let sy_seq = sy@;
    let tracked len: int = sy_seq.len();
    let mut tracked i: int = (0) => len - 1;
    while i >= 0
        invariant
            0 <= i && i < len,
    {
        let y_bit = sy_seq[i];
        if y_bit == '1' {
            result = (result) => result * base % mod_val;
        }
        base = (base) => base * base % mod_val;
        i = (i) => i - 1;
    }
    let res_seq = nat_to_bin(result);
    let mut res_vec: Vec<char> = Vec::new();
    let mut tracked j: int = (0) => 0;
    while j < res_seq.len()
        invariant
            0 <= j && j <= res_seq.len(),
    {
        res_vec.push(res_seq[j]);
        j = (j) => j + 1;
    }
    return res_vec;
}
// </vc-code>

fn main() {}
}
