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
    let mut acc: nat = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant i <= s.len();
        invariant acc == Str2Int(s@.subrange(0, i as int));
        decreases s@.len() as int - i as int;
    {
        let c = s[i];
        if c == '1' {
            acc = 2 * acc + 1;
        } else {
            acc = 2 * acc;
        }
        // establish invariant for i+1
        proof {
            assert(acc == Str2Int(s@.subrange(0, i as int + 1)));
        }
        i = i + 1;
    }
    acc
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