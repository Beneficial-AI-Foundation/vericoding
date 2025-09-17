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
/* helper modified by LLM (iteration 2): fixed nat/integer mismatches */
fn run_Str2Int(s: &[char]) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        let n = run_Str2Int(&s[0..s.len()-1]);
        let last: nat = if s[s.len()-1] == '1' { 1nat } else { 0nat };
        2nat * n + last
    }
}

/* helper modified by LLM (iteration 2): convert nat to bits using nat literals */
fn nat_to_bits(n: nat) -> Vec<char>
    decreases n
{
    if n == 0nat {
        let mut v = Vec::<char>::new();
        v.push('0');
        v
    } else {
        let mut v = nat_to_bits(n / 2nat);
        let bit = if n % 2nat == 1nat { '1' } else { '0' };
        v.push(bit);
        v
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): corrected nat literals and modular loop */
    let x = run_Str2Int(sx);
    let y = run_Str2Int(sy);
    let m = run_Str2Int(sz);
    let mut res_nat: nat = 1nat % m;
    let mut i: nat = 0nat;
    while i < y
        invariant
            i <= y,
        decreases
            y - i
    {
        res_nat = (res_nat * x) % m;
        i = i + 1nat;
    }
    let res = nat_to_bits(res_nat);
    res
}
// </vc-code>

fn main() {}
}
