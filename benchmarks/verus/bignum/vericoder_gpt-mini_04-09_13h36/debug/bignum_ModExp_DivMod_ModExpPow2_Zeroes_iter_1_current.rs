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
exec fn bits_to_nat(s: &[char]) -> (n: nat)
  requires ValidBitString(s@)
  ensures n == Str2Int(s@)
{
    let mut acc: nat = 0;
    let mut i: nat = 0;
    while i < s.len() as nat
        invariant ValidBitString(s@)
        invariant acc == Str2Int(s@.subrange(0, i as int))
    {
        let bit_ch = s[i as usize];
        if bit_ch == '1' {
            acc = 2 * acc + 1;
        } else {
            acc = 2 * acc;
        }
        i = i + 1;
    }
    acc
}

exec fn pow_full(base: nat, exp: nat) -> (r: nat)
  decreases exp
  ensures r == Exp_int(base, exp)
{
    if exp == 0 {
        1
    } else {
        let t = pow_full(base, exp - 1);
        base * t
    }
}

exec fn nat_to_bits(n: nat) -> (v: Vec<char>)
  decreases n
  ensures Str2Int(v@) == n
  ensures ValidBitString(v@)
{
    if n == 0 {
        Vec::<char>::new()
    } else {
        let mut prev = nat_to_bits(n / 2);
        let ch = if n % 2 == 1 { '1' } else { '0' };
        prev.push(ch);
        prev
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
    let x = bits_to_nat(sx);
    let y = bits_to_nat(sy);
    let m = bits_to_nat(sz);

    let full = pow_full(x, y);
    let res_nat = full % m;
    let res_vec = nat_to_bits(res_nat);

    proof {
        assert(x == Str2Int(sx@));
        assert(y == Str2Int(sy@));
        assert(m == Str2Int(sz@));
        assert(full == Exp_int(x, y));
        assert(Str2Int(res_vec@) == res_nat);
        assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@) == res_nat);
    }

    return res_vec;
}
// </vc-code>

fn main() {}
}