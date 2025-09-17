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
/* helper modified by LLM (iteration 6): fixed nat type mismatches by casting integer literals to nat */
exec fn exec_str_to_int(s: &[char]) -> nat
{
    let mut n: nat = 0 as nat;
    for i in 0..s.len()
    {
        n = n * (2 as nat);
        if s[i] == '1' {
            n = n + (1 as nat);
        }
    }
    n
}

/* helper modified by LLM (iteration 6): fixed nat type mismatches by casting integer literals to nat */
exec fn exec_int_to_str(n: nat) -> Vec<char>
{
    if n == (0 as nat) {
        return Vec::new();
    }
    let mut s: Vec<char> = Vec::new();
    let mut x = n;
    while x > (0 as nat)
    {
        if x % (2 as nat) == (1 as nat) {
            s.push('1');
        } else {
            s.push('0');
        }
        x = x / (2 as nat);
    }
    s.reverse();
    s
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 6): fixed nat type mismatches by casting integer literals to nat */
{
    let base_val = exec_str_to_int(sx);
    let exp_val = exec_str_to_int(sy);
    let modulus_val = exec_str_to_int(sz);

    let mut result: nat = 1 as nat;
    let mut base_power = base_val % modulus_val;
    let mut exp_remaining = exp_val;

    while exp_remaining > (0 as nat)
        invariant
            result * Exp_int(base_power, exp_remaining) % modulus_val == Exp_int(base_val, exp_val) % modulus_val,
            base_power < modulus_val,
        decreases exp_remaining
    {
        if exp_remaining % (2 as nat) == (1 as nat) {
            result = (result * base_power) % modulus_val;
        }
        base_power = (base_power * base_power) % modulus_val;
        exp_remaining = exp_remaining / (2 as nat);
    }

    let res_vec = exec_int_to_str(result);
    res_vec
}
// </vc-code>

fn main() {}
}
