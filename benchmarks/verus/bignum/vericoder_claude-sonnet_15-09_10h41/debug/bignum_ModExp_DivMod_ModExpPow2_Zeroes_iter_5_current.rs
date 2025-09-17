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
/* helper modified by LLM (iteration 5): fixed nat literal comparisons */
fn mod_operation(a: &[char], m: &[char]) -> (result: Vec<char>)
    requires ValidBitString(a@), ValidBitString(m@), Str2Int(m@) > 0,
    ensures ValidBitString(result@), Str2Int(result@) == Str2Int(a@) % Str2Int(m@)
{
    let a_val = Str2Int(a@);
    let m_val = Str2Int(m@);
    let result_val = a_val % m_val;
    int_to_bitstring(result_val)
}

fn divide_by_2(s: &[char]) -> (result: Vec<char>)
    requires ValidBitString(s@), s@.len() > 0,
    ensures ValidBitString(result@), Str2Int(result@) == Str2Int(s@) / 2
{
    if s.len() == 1 {
        vec!['0']
    } else {
        s[0..s.len()-1].to_vec()
    }
}

fn multiply_mod(a: &[char], b: &[char], m: &[char]) -> (result: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@), ValidBitString(m@), Str2Int(m@) > 0,
    ensures ValidBitString(result@), Str2Int(result@) == (Str2Int(a@) * Str2Int(b@)) % Str2Int(m@)
{
    let a_val = Str2Int(a@);
    let b_val = Str2Int(b@);
    let m_val = Str2Int(m@);
    let result_val = (a_val * b_val) % m_val;
    int_to_bitstring(result_val)
}

fn int_to_bitstring(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@), Str2Int(result@) == n
{
    if n == 0nat {
        vec!['0']
    } else {
        let mut result = Vec::new();
        let mut temp = n;
        while temp > 0nat
            invariant ValidBitString(result@)
        {
            if temp % 2nat == 1nat {
                result.insert(0, '1');
            } else {
                result.insert(0, '0');
            }
            temp = temp / 2nat;
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed nat literal comparisons */
    if sy.len() == 0 {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    if Str2Int(sy@) == 0nat {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    if Str2Int(sy@) == 1nat {
        let base_mod = mod_operation(sx, sz);
        return base_mod;
    }
    
    let half_exp = divide_by_2(sy);
    let half_result = ModExp_DivMod_ModExpPow2_Zeroes(sx, &half_exp, sz);
    let squared = multiply_mod(&half_result, &half_result, sz);
    
    if sy[sy.len() - 1] == '1' {
        let base_mod = mod_operation(sx, sz);
        multiply_mod(&squared, &base_mod, sz)
    } else {
        squared
    }
}
// </vc-code>

fn main() {}
}
