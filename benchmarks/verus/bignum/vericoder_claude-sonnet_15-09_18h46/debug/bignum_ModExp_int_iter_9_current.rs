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
/* helper modified by LLM (iteration 9): fixed nat literals using proper syntax */
fn vec_from_bit_string(s: &[char]) -> (result: Vec<char>)
    requires ValidBitString(s@)
    ensures ValidBitString(result@),
            result@.len() == s@.len(),
            forall |i: int| 0 <= i < s@.len() ==> result@[i] == s@[i]
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(result@),
            result@.len() == i,
            forall |j: int| 0 <= j < i ==> result@[j] == s@[j]
    {
        result.push(s[i]);
        i += 1;
    }
    result
}

fn nat_to_bit_vec(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@)
{
    if n == 0 {
        vec!['0']
    } else {
        let mut result = Vec::new();
        let mut num = n;
        while num > 0
            invariant ValidBitString(result@)
            decreases num
        {
            if num % 2 == 0 {
                result.push('0');
            } else {
                result.push('1');
            }
            num = num / 2;
        }
        result.reverse();
        result
    }
}

proof fn lemma_exp_mod_base_case(x: nat, z: nat)
    requires z > 1
    ensures Exp_int(x, 0) % z == 1 % z
{
}

proof fn lemma_exp_mod_recursive(x: nat, y: nat, z: nat)
    requires y > 0, z > 1
    ensures Exp_int(x, y) % z == (x * Exp_int(x, (y - 1) as nat)) % z
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
    /* code modified by LLM (iteration 9): fixed nat literals using proper syntax */
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
    let mut result: nat = 1;
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
    
    nat_to_bit_vec(result)
}
// </vc-code>

fn main() {}
}
