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
/* helper modified by LLM (iteration 9): added explicit type annotation 'u64' to closure parameter in ensures clause to fix compilation error */
exec fn mod_mul_u64(a: u64, b: u64, m: u64) -> u64
    requires
        m > 1,
        a < m,
        b < m,
    ensures (|result: u64| (result as nat) == (a as nat) * (b as nat) % (m as nat))
{
    let prod = ((a as u128) * (b as u128)) % (m as u128);
    return (prod as u64);
}

/* helper modified by LLM (iteration 9): added explicit type annotation 'u64' to closure parameter in ensures clause to fix compilation error */
exec fn pow_mod(base: u64, exp: u64, m: u64) -> u64
    requires
        m > 1,
        base < m,
    ensures (|result: u64| (result as nat) == Exp_int(base as nat, exp as nat) % (m as nat))
    decreases exp
{
    if exp == 0 {
        return 1;
    } else if exp % 2 == 0 {
        let half = pow_mod(base, exp / 2, m);
        return mod_mul_u64(half, half, m);
    } else {
        let half = pow_mod(base, exp / 2, m);
        let hh = mod_mul_u64(half, half, m);
        return mod_mul_u64(hh, base, m);
    }
}

/* helper modified by LLM (iteration 8): added decreases clause for recursive call */
exec fn bit_str_to_nat(s: &[char]) -> (res: u64)
    decreases s.len()
{
    if s.len() == 0 {
        return 0;
    } else {
        let rest = bit_str_to_nat(&s[0..s.len() - 1]);
        return 2 * rest + if s[s.len() - 1] == '1' { 1 } else { 0 };
    }
}

/* helper modified by LLM (iteration 8): fixed invariant syntax and added decreases clause */
exec fn nat_to_bit_str(n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == (n as nat)
{
    if n == 0 {
        return vec!['0'];
    } else {
        let mut s = vec![];
        let mut num = n;
        while num > 0
            invariant num as nat <= n as nat
            decreases num
        {
            s.push(if num % 2 == 1 { '1' } else { '0' });
            num = num / 2;
        }
        s.reverse();
        return s;
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): unchanged, compilation errors in ensures clauses of helpers fixed */
{
    let m = bit_str_to_nat(sz);
    let a = bit_str_to_nat(sx);
    let b = bit_str_to_nat(sy);
    let base = a % m;
    let result = pow_mod(base, b, m);
    return nat_to_bit_str(result);
}
// </vc-code>

fn main() {}
}
