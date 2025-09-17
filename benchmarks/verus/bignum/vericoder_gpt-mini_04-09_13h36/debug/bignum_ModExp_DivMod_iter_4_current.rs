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
exec fn parse_bits(s: &[char]) -> nat
  requires ValidBitString(s@)
  ensures result == Str2Int(s@)
  decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let first = s[0];
        let tail = &s[1..];
        let tail_val = parse_bits(tail);
        let pow = pow_nat(2, (s.len() - 1) as nat);
        let bit = if first == '1' { 1 } else { 0 };
        pow * bit + tail_val
    }
}

exec fn pow_nat(x: nat, y: nat) -> nat
  ensures result == Exp_int(x, y)
  decreases y
{
    if y == 0 {
        1
    } else {
        x * pow_nat(x, y - 1)
    }
}

exec fn nat_to_bits(n: nat) -> Vec<char>
  ensures Str2Int(result@) == n
  ensures ValidBitString(result@)
  decreases n
{
    if n == 0 {
        Vec::<char>::new()
    } else {
        let q = n / 2;
        let r = n % 2;
        let mut v = nat_to_bits(q);
        if r == 1 {
            v.push('1');
        } else {
            v.push('0');
        }
        v
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_nat = parse_bits(sx);
    let y_nat = parse_bits(sy);
    let z_nat = parse_bits(sz);

    let pow = pow_nat(x_nat, y_nat);
    let r = pow % z_nat;

    let resv = nat_to_bits(r);

    proof {
        // connect parsed values to specs
        assert(x_nat == Str2Int(sx@));
        assert(y_nat == Str2Int(sy@));
        assert(z_nat == Str2Int(sz@));
        // pow corresponds to Exp_int
        assert(pow == Exp_int(x_nat, y_nat));
        // combine to get modular equality
        assert(pow % z_nat == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
        // nat_to_bits returns correct Str2Int and valid bitstring
        assert(Str2Int(resv@) == r);
        assert(ValidBitString(resv@));
        // final equality
        assert(Str2Int(resv@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }

    resv
}
// </vc-code>

fn main() {}
}