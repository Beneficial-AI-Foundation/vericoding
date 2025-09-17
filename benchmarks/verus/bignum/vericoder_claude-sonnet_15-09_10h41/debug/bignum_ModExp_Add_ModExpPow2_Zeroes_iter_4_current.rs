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
/* helper modified by LLM (iteration 4): fixed nat literals by removing 'nat' suffix */
spec fn pow_mod_property(base: nat, exp: nat, modulus: nat) -> bool {
    modulus > 1 ==> Exp_int(base, exp) % modulus < modulus
}

proof fn exp_int_base_case(x: nat)
    ensures Exp_int(x, 0) == 1
{
}

proof fn exp_int_recursive_case(x: nat, y: nat)
    requires y > 0
    ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
}

proof fn str2int_empty_case(s: Seq<char>)
    requires s.len() == 0
    ensures Str2Int(s) == 0
{
}

proof fn str2int_nonempty_case(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0
    ensures Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1 } else { 0 })
{
}

proof fn valid_bit_string_subrange(s: Seq<char>, start: int, end: int)
    requires ValidBitString(s), 0 <= start <= end <= s.len()
    ensures ValidBitString(s.subrange(start, end))
{
}

fn nat_to_binary_string(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@), Str2Int(result@) == n
{
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        result
    } else {
        let mut result = Vec::new();
        let mut temp = n;
        while temp > 0
            invariant temp <= n
        {
            if temp % 2 == 1 {
                result.push('1');
            } else {
                result.push('0');
            }
            temp = temp / 2;
        }
        result.reverse();
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed nat literals by removing 'nat' suffix */
{
    if sy.len() == 1 && sy[0] == '0' {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    let base_mod = Str2Int(sx@) % Str2Int(sz@);
    let mut result_val: nat = 1;
    let base = base_mod;
    let exp = Str2Int(sy@);
    let modulus = Str2Int(sz@);
    
    let mut i: nat = 0;
    while i < exp
        invariant
            result_val == Exp_int(base_mod, i) % modulus,
            modulus > 1,
            i <= exp
    {
        result_val = (result_val * base) % modulus;
        i = i + 1;
    }
    
    nat_to_binary_string(result_val)
}
// </vc-code>

fn main() {}
}
