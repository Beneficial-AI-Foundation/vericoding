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
/* helper modified by LLM (iteration 7): replaced nat with u64 for exec code compatibility */
exec fn exec_str_to_int(s: &[char]) -> u64
{
    let mut n: u64 = 0u64;
    for i in 0..s.len()
    {
        n = n * 2u64;
        if s[i] == '1' {
            n = n + 1u64;
        }
    }
    n
}

/* helper modified by LLM (iteration 10): replaced reverse with manual loop to avoid unsupported &mut parameter */
exec fn exec_int_to_str(n: u64) -> Vec<char>
{
    if n == 0u64 {
        return Vec::new();
    }
    let mut s: Vec<char> = Vec::new();
    let mut x = n;
    while x > 0u64
    {
        if x % 2u64 == 1u64 {
            s.push('1');
        } else {
            s.push('0');
        }
        x = x / 2u64;
    }
    // Instead of s.reverse(), we build a new vector by iterating from the end to the beginning.
    let mut result_vec: Vec<char> = Vec::new();
    let mut i = s.len() as int;
    while i > 0
    {
        i = i - 1;
        result_vec.push(s[i as usize]);
    }
    result_vec
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 7): replaced nat with u64 for exec code compatibility and updated invariant with casts */
{
    let base_val = exec_str_to_int(sx);
    let exp_val = exec_str_to_int(sy);
    let modulus_val = exec_str_to_int(sz);

    let mut result: u64 = 1u64;
    let mut base_power = base_val % modulus_val;
    let mut exp_remaining = exp_val;

    while exp_remaining > 0u64
        invariant
            ((result as nat) * Exp_int(base_power as nat, exp_remaining as nat)) % (modulus_val as nat) == Exp_int(base_val as nat, exp_val as nat) % (modulus_val as nat),
            (base_power as nat) < (modulus_val as nat),
        decreases exp_remaining as nat
    {
        if exp_remaining % 2u64 == 1u64 {
            result = (result * base_power) % modulus_val;
        }
        base_power = (base_power * base_power) % modulus_val;
        exp_remaining = exp_remaining / 2u64;
    }

    let res_vec = exec_int_to_str(result);
    res_vec
}
// </vc-code>

fn main() {}
}
