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
        let last = s[s.len() - 1];
        let rest = &s[..s.len() - 1];
        let tail_val = parse_bits(rest);
        let bit = if last == '1' { 1 } else { 0 };
        2 * tail_val + bit
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
        let v = Vec::<char>::new();
        proof {
            assert(Str2Int(v@) == 0);
            assert(ValidBitString(v@));
        }
        v
    } else {
        let q = n / 2;
        let r = n % 2;
        let mut v = nat_to_bits(q);
        let pre_len = v.len();
        if r == 1 {
            v.push('1');
        } else {
            v.push('0');
        }
        // Prove the postconditions using the recursive postcondition and definition of Str2Int
        proof {
            // old vector (before push) satisfied Str2Int == q and ValidBitString
            // we use the fact that subrange(0, pre_len) corresponds to that old vector
            let old_seq = v@.subrange(0, pre_len as int);
            let last_char = v@.index(pre_len as int);
            // By the postcondition of the recursive call on q we have:
            assert(Str2Int(old_seq) == q);
            assert(ValidBitString(old_seq));
            if last_char == '1' {
                assert(Str2Int(v@) == 2 * Str2Int(old_seq) + 1);
            } else {
                assert(Str2Int(v@) == 2 * Str2Int(old_seq) + 0);
            }
            assert(Str2Int(v@) == 2 * q + r);
            assert(Str2Int(v@) == n);
            assert(ValidBitString(v@));
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
    exec fn ModExp_DivMod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
      requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
      ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
      decreases sy@.len()
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
}
// </vc-code>

fn main() {}
}