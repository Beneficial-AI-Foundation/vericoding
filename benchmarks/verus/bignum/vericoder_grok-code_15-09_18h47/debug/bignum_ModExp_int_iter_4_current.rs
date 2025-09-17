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
/* helper modified by LLM (iteration 4): removed invalid nat suffixes and used as nat casts */
exec fn get_int(s: &[char]) -> (res: nat)
    requires
        ValidBitString(s@),
    ensures
        get_int(s) == Str2Int(s@),
    decreases s.len()
{
    if s.len() == 0 {
        0 as nat
    } else {
        (2 as nat) * get_int(&s[0..s.len() - 1]) + if s[s.len() - 1] == '1' { 1 as nat } else { 0 as nat }
    }
}

/* helper modified by LLM (iteration 4): removed invalid nat suffixes and used as nat casts */
fn mul_mod(a: nat, b: nat, m: nat) -> (res: nat)
    requires
        m > 1,
    ensures
        mul_mod(a, b, m) == (a * b) % m,
{
    let a_mod = a % m;
    let b_mod = b % m;
    (a_mod * b_mod) % m
}

/* helper modified by LLM (iteration 4): removed invalid nat suffixes and used as nat casts */
fn pow_mod(base: nat, exp: nat, m: nat) -> (res: nat)
    requires
        m > 1,
    ensures
        pow_mod(base, exp, m) == Exp_int(base, exp) % m,
    decreases exp
{
    if exp == 0 as nat {
        1 as nat
    } else {
        let half = pow_mod(base, exp / (2 as nat), m);
        let sq = mul_mod(half, half, m);
        if exp % (2 as nat) == 0 as nat {
            sq
        } else {
            mul_mod(sq, base, m)
        }
    }
}

/* helper modified by LLM (iteration 4): removed invalid nat suffixes and used as nat casts */
exec fn int_to_vec(n: nat) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n,
    decreases n
{
    if n == 0 as nat {
        Vec::new()
    } else {
        let quot = n / (2 as nat);
        let rem = n % (2 as nat);
        let mut higher = int_to_vec(quot);
        let bit = if rem == 1 as nat { '1' } else { '0' };
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
    /* code modified by LLM (iteration 4): relied on fixed helpers */
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
