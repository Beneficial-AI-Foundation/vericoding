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
/* helper modified by LLM (iteration 5): Added nat suffixes to integer literals to match nat types */
exec fn str_to_nat(s: &[char]) -> nat
    requires ValidBitString(s@)
    ensures str_to_nat(s) == Str2Int(s@)
{
    let mut result: nat = 0nat;
    let mut i = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            result == Str2Int(s@.subrange(0, i as int))
        decreases s.len() - i
    {
        result = result * 2nat + (if s[i] == '1' { 1nat } else { 0nat });
        i += 1;
    }
    result
}

/* helper modified by LLM (iteration 5): Added nat suffixes to integer literals to match nat types */
exec fn mod_exp(base: nat, exp: nat, modd: nat) -> nat
    requires base >= 0nat, exp >= 0nat, modd > 1nat
    ensures mod_exp(base, exp, modd) == Exp_int(base, exp) % modd
    decreases exp
{
    if exp == 0nat {
        1nat
    } else {
        let res = mod_exp(base, exp / 2nat, modd);
        let res2 = (res * res) % modd;
        if exp % 2nat == 0nat {
            res2
        } else {
            (res2 * base) % modd
        }
    }
}

/* helper modified by LLM (iteration 5): Added nat suffixes to integer literals to match nat types */
exec fn nat_to_binary(n: nat) -> Vec<char>
    requires n >= 0nat
    ensures ValidBitString(nat_to_binary(n)@), Str2Int(nat_to_binary(n)@) == n
{
    if n == 0nat {
        return vec!['0'];
    } else {
        let mut string = Vec::new();
        let mut num: nat = n;
        while num > 0nat
            invariant num >= 0nat
            decreases num
        {
            let bit = if num % 2nat == 0nat { '0' } else { '1' };
            string.push(bit);
            num = num / 2nat;
        }
        string.reverse();
        return string;
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No changes needed, compilation errors fixed in helpers */
{
    let base = str_to_nat(sx);
    let expp = str_to_nat(sy);
    let modd = str_to_nat(sz);
    let res_int = mod_exp(base, expp, modd);
    let res = nat_to_binary(res_int);
    res
}
// </vc-code>

fn main() {}
}
