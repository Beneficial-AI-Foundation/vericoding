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
/* helper modified by LLM (iteration 4): fixed type errors by using usize for loop variables and adjusting blow invariants */
exec fn string_to_nat(s: &[char]) -> int
    requires
        ValidBitString(s@)
    ensures
        result == Str2Int(s@),
        0 <= result
    decreases s.len()
{
    let mut result = 0;
    let mut pow = 1;
    let mut i = s.len() - 1;
    while i as int >= 0
        invariant
            0 <= i < s.len()
        decreases i
    {
        if s@[i as int] == '1' {
            result = result + pow;
        }
        pow = pow * 2;
        i = i - 1;
    }
    return result;
}

/* helper modified by LLM (iteration 4): fixed type errors by using usize for loop variables */
exec fn pow_mod(base: int, exp_bits: &[char], modulus: int) -> int
    requires
        ValidBitString(exp_bits@),
        exp_bits@.len() > 0,
        modulus > 1,
        base >= 0
    ensures
        result == Exp_int(base as nat, Str2Int(exp_bits@)) % (modulus as nat),
        result >= 0
    decreases exp_bits.len()
{
    let mut result = 1;
    let mut current_base = base % modulus;
    let mut i = exp_bits.len() - 1;
    while i as int >= 0
        invariant
            0 <= i < exp_bits.len()
        decreases i
    {
        if exp_bits@[i as int] == '1' {
            result = (result * current_base) % modulus;
        }
        current_base = (current_base * current_base) % modulus;
        i = i - 1;
    }
    return result;
}

/* helper modified by LLM (iteration 4): no changes needed, added comment */
exec fn nat_to_bitstring(n: int) -> Vec<char>
    requires n >= 0
    ensures
        ValidBitString(result@),
        Str2Int(result@) == n
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        return v;
    }
    let mut v = Vec::new();
    let mut num = n;
    while num > 0
        decreases num
    {
        v.push(if num % 2 == 0 { '0' } else { '1' });
        num = num / 2;
    }
    v.reverse();
    return v;
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): updated to call fixed string_to_nat and pow_mod helpers */
{
    let x = string_to_nat(sx);
    let z = string_to_nat(sz);
    let exp_mod = pow_mod(x, sy, z);
    let res = nat_to_bitstring(exp_mod);
    return res;
}
// </vc-code>

fn main() {}
}
