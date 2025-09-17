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
/* helper modified by LLM (iteration 3): fixed nat suffix by using 'as nat' */
fn str2int_exec(s: &[char]) -> (result: nat)
    requires ValidBitString(s@)
    ensures result == Str2Int(s@)
    decreases s.len()
{
    if s.len() == 0 {
        0 as nat
    } else {
        let last = s[s.len()-1];
        let rest = &s[0..s.len()-1];
        let rest_val = str2int_exec(rest);
        if last == '1' {
            2 as nat * rest_val + 1 as nat
        } else {
            2 as nat * rest_val
        }
    }
}

/* helper modified by LLM (iteration 3): fixed nat suffix by using 'as nat' */
fn int2str_exec(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@), Str2Int(result@) == n
    decreases n
{
    if n == 0 as nat {
        vec!['0']
    } else if n == 1 as nat {
        vec!['1']
    } else {
        let last_bit = if n % 2 as nat == 1 as nat { '1' } else { '0' };
        let rest = n / 2 as nat;
        let mut rest_str = int2str_exec(rest);
        rest_str.push(last_bit);
        rest_str
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed nat suffix by using 'as nat' */
{
    if sy.len() == 1 {
        let base_int = str2int_exec(sx);
        let modulus_int = str2int_exec(sz);
        let result_int = if sy[0] == '1' {
            base_int % modulus_int
        } else {
            1 as nat % modulus_int
        };
        int2str_exec(result_int)
    } else {
        let last_bit = sy[sy.len()-1];
        let rest_exp = &sy[0..sy.len()-1];
        let temp_result = ModExp_ModExpPow2_Mul(sx, rest_exp, sz);
        let temp_int = str2int_exec(&temp_result);
        let base_int = str2int_exec(sx);
        let modulus_int = str2int_exec(sz);
        let squared = (temp_int * temp_int) % modulus_int;
        let base_mod = base_int % modulus_int;
        let result_int = if last_bit == '1' {
            (squared * base_mod) % modulus_int
        } else {
            squared
        };
        int2str_exec(result_int)
    }
}
// </vc-code>

fn main() {}
}
