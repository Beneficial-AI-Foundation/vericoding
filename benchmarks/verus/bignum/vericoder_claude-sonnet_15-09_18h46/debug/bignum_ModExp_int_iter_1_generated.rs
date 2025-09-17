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
spec fn bit_string_to_vec(s: Seq<char>) -> Vec<char>
    requires ValidBitString(s)
    ensures ValidBitString(result@),
            result@.len() == s.len(),
            forall |i: int| 0 <= i < s.len() ==> result@[i] == s[i]
{
    Vec::from_seq(s)
}

spec fn nat_to_bit_string(n: nat) -> Seq<char>
    ensures ValidBitString(nat_to_bit_string(n))
{
    if n == 0 {
        seq!['0']
    } else if n == 1 {
        seq!['1']
    } else {
        nat_to_bit_string(n / 2).add(seq![if n % 2 == 0 { '0' } else { '1' }])
    }
}

lemma lemma_exp_mod_base_case(x: nat, z: nat)
    requires z > 1
    ensures Exp_int(x, 0) % z == 1 % z
{
}

lemma lemma_exp_mod_recursive(x: nat, y: nat, z: nat)
    requires y > 0, z > 1
    ensures Exp_int(x, y) % z == (x * Exp_int(x, y - 1)) % z
{
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 0 {
        return vec!['1'];
    }
    
    let sx_int = Str2Int(sx@);
    let sy_int = Str2Int(sy@);
    let sz_int = Str2Int(sz@);
    
    if sy_int == 0 {
        return vec!['1'];
    }
    
    let base_mod = sx_int % sz_int;
    let mut result = 1nat;
    let mut base = base_mod;
    let mut exp = sy_int;
    
    while exp > 0
        invariant
            result * Exp_int(base, exp) % sz_int == Exp_int(sx_int, sy_int) % sz_int,
            sz_int > 1
        decreases exp
    {
        if exp % 2 == 1 {
            result = (result * base) % sz_int;
        }
        base = (base * base) % sz_int;
        exp = exp / 2;
    }
    
    let result_string = nat_to_bit_string(result);
    Vec::from_seq(result_string)
}
// </vc-code>

fn main() {}
}
