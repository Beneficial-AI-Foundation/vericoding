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
exec fn seq_to_nat(s: &[char]) -> (result: nat)
  requires ValidBitString(s@)
  ensures result == Str2Int(s@)
  decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        let n = s.len();
        let last = s[n - 1];
        let prefix = seq_to_nat(&s[..n - 1]);
        if last == '1' {
            2nat * prefix + 1nat
        } else {
            2nat * prefix
        }
    }
}

exec fn full_exp(x: nat, y: nat) -> (result: nat)
  ensures result == Exp_int(x, y)
  decreases y
{
    if y == 0nat {
        1nat
    } else {
        x * full_exp(x, y - 1nat)
    }
}

exec fn nat_to_seq(n: nat) -> (result: Vec<char>)
  ensures Str2Int(result@) == n && ValidBitString(result@)
  decreases n
{
    if n == 0nat {
        Vec::<char>::new()
    } else {
        let q = n / 2nat;
        let r = n % 2nat;
        let mut v = nat_to_seq(q);
        if r == 1nat {
            v.push('1');
        } else {
            v.push('0');
        }
        v
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
{
    let x = seq_to_nat(sx);
    let y = seq_to_nat(sy);
    let z = seq_to_nat(sz);
    let e = full_exp(x, y);
    let r = e % z;
    let res = nat_to_seq(r);
    proof {
        // relate computed values to their specifications
        assert(x == Str2Int(sx@));
        assert(y == Str2Int(sy@));
        assert(z == Str2Int(sz@));
        assert(e == Exp_int(x, y));
        // nat_to_seq ensures the sequence encodes r
        assert(Str2Int(res@) == r);
        // combine equalities to reach the required postcondition
        assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) == e);
        assert(Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@) == r);
        assert(ValidBitString(res@));
    }
    return res;
}
// </vc-code>

fn main() {}
}