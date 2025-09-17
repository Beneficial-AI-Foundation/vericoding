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
/* helper modified by LLM (iteration 5): fixed compilation errors by changing exec types to u64 to avoid using 'nat' in exec code */
exec fn get_int(s: &[char]) -> (res: u64)
    requires
        ValidBitString(s@),
    ensures
        get_int(s) == Str2Int(s@) as u64,
    decreases s
{
    if s.len() == 0 {
        0
    } else {
        2 * get_int(&s[0..s.len() - 1]) + if s[s.len() - 1] == '1' { 1 } else { 0 }
    }
}

/* helper modified by LLM (iteration 5): fixed compilation errors by changing exec types to u64 to avoid using 'nat' in exec code */
exec fn mul_mod(a: u64, b: u64, m: u64) -> (res: u64)
    requires
        m > 1,
    ensures
        (a as nat * b as nat) % m as nat == mul_mod(a, b, m) as nat,
{
    let a_mod = a % m;
    let b_mod = b % m;
    (a_mod * b_mod) % m
}

/* helper modified by LLM (iteration 5): fixed compilation errors by changing exec types to u64 to avoid using 'nat' in exec code */
exec fn pow_mod(base: u64, exp: u64, m: u64) -> (res: u64)
    requires
        m > 1,
    ensures
        pow_mod(base, exp, m) as nat == Exp_int(base as nat, exp as nat) % (m as nat),
    decreases exp
{
    if exp == 0 {
        1
    } else {
        let half = pow_mod(base, exp / 2, m);
        let sq = mul_mod(half, half, m);
        if exp % 2 == 0 {
            sq
        } else {
            mul_mod(sq, base, m)
        }
    }
}

/* helper modified by LLM (iteration 5): fixed compilation errors by changing exec types to u64 to avoid using 'nat' in exec code */
exec fn int_to_vec(n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n as nat,
    decreases n
{
    if n == 0 {
        Vec::new()
    } else {
        let quot = n / 2;
        let rem = n % 2;
        let mut higher = int_to_vec(quot);
        let bit = if rem == 1 { '1' } else { '0' };
        higher.push(bit);
        higher
    }
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
    /* code modified by LLM (iteration 5): ensured correct types after fixing helpers to use u64 */
    let base = get_int(sx);
    let exp = get_int(sy);
    let m = get_int(sz);
    let res_num = pow_mod(base, exp, m);
    let res = int_to_vec(res_num);
    res
}
// </vc-code>

fn main() {}
}
