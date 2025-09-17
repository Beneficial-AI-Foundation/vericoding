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
proof fn lemma_exp_properties(x: nat, y: nat, z: nat)
    requires z > 1
    ensures
        y > 0 ==> Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat),
        Exp_int(x, 0) == 1,
{
}

proof fn lemma_mod_properties(a: nat, b: nat, c: nat, m: nat)
    requires m > 1
    ensures
        (a * b) % m == ((a % m) * (b % m)) % m,
        (a + b) % m == ((a % m) + (b % m)) % m,
{
}

/* helper modified by LLM (iteration 2): Fixed type errors in int_to_bit_string */
exec fn int_to_bit_string(n: nat) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n,
    decreases n
{
    if n == 0nat {
        vec!['0']
    } else if n == 1nat {
        vec!['1']
    } else {
        let mut res = int_to_bit_string((n / 2) as nat);
        if n % 2 == 0nat {
            res.push('0');
        } else {
            res.push('1');
        }
        res
    }
}

exec fn mod_mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(sx@),
        ValidBitString(sy@),
        ValidBitString(sz@),
        Str2Int(sz@) > 1,
    ensures
        ValidBitString(res@),
        Str2Int(res@) == (Str2Int(sx@) * Str2Int(sy@)) % Str2Int(sz@),
{
    proof {
        lemma_mod_properties(Str2Int(sx@), Str2Int(sy@), 0, Str2Int(sz@));
    }
    let prod = (Str2Int(sx@) * Str2Int(sy@)) % Str2Int(sz@);
    int_to_bit_string(prod)
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed type errors and indexing issues */
    if sy@.len() == 1nat {
        if sy@.index(0) == '0' {
            proof {
                lemma_exp_properties(Str2Int(sx@), 0, Str2Int(sz@));
            }
            return int_to_bit_string(1nat);
        } else {
            proof {
                lemma_exp_properties(Str2Int(sx@), 1, Str2Int(sz@));
            }
            return int_to_bit_string(Str2Int(sx@) % Str2Int(sz@));
        }
    }
    
    let sy_prefix = &sy[0..sy.len() - 1];
    let last_bit = sy[sy.len() - 1];
    
    let half_exp = ModExp_Mul_Zeroes(sx, sy_prefix, sz);
    let squared = mod_mul(&half_exp, &half_exp, sz);
    
    if last_bit == '1' {
        let sx_mod = int_to_bit_string(Str2Int(sx@) % Str2Int(sz@));
        proof {
            lemma_exp_properties(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
            lemma_mod_properties(Exp_int(Str2Int(sx@), Str2Int(sy@) / 2) * Exp_int(Str2Int(sx@), Str2Int(sy@) / 2), Str2Int(sx@), 0, Str2Int(sz@));
        }
        mod_mul(&squared, &sx_mod, sz)
    } else {
        proof {
            lemma_exp_properties(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
        }
        squared
    }
}
// </vc-code>

fn main() {}
}
