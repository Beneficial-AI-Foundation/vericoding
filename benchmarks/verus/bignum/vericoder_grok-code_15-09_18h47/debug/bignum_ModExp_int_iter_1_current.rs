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
exec fn get_int(s: &[char]) -> (res: nat)
    requires
        ValidBitString(s@),
    ensures
        get_int(s) == Str2Int(s@),
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        2nat * get_int(&s[0..s.len() - 1]) + if s[s.len() - 1] == '1' { 1nat } else { 0nat }
    }
}

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

fn pow_mod(base: nat, exp: nat, m: nat) -> (res: nat)
    requires
        m > 1,
    ensures
        pow_mod(base, exp, m) == Exp_int(base, exp) % m,
    decreases exp
{
    if exp == 0 {
        1nat
    } else {
        let half = pow_mod(base, exp / 2nat, m);
        let sq = mul_mod(half, half, m);
        if exp % 2nat == 0 {
            sq
        } else {
            mul_mod(sq, base, m)
        }
    }
}

exec fn int_to_bit(n: nat) -> (res: Seq<char>)
    ensures
        ValidBitString(res),
        Str2Int(res) == n,
{
    if n == 0nat {
        Seq::empty()
    } else {
        let quot = n / 2nat;
        let rem = n % 2nat;
        let higher = int_to_bit(quot);
        let bit = if rem == 1 { '1' } else { '0' };
        higher.concat(Seq::singleton(bit))
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
    let base = get_int(sx);
    let exp = get_int(sy);
    let m = get_int(sz);
    let res_num = pow_mod(base, exp, m);
    let s = int_to_bit(res_num);
    Vec::from_seq(s)
}
// </vc-code>

fn main() {}
}
