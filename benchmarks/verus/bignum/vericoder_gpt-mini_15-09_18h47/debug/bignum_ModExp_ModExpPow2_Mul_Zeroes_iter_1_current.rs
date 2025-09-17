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
fn Str2Int_exec(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let prefix = s.subrange(0, s.len() as int - 1);
        2 * Str2Int_exec(prefix) + (if s.index(s.len() as int - 1) == '1' { 1 } else { 0 })
    }
}

proof fn str2int_equiv(s: Seq<char>)
    requires ValidBitString(s),
    ensures Str2Int(s) == Str2Int_exec(s),
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        let prefix = s.subrange(0, s.len() as int - 1);
        str2int_equiv(prefix);
        proof {
            assert(Str2Int(s) == 2 * Str2Int(prefix) + (if s.index(s.len() as int - 1) == '1' { 1 } else { 0 }));
            assert(Str2Int_exec(s) == 2 * Str2Int_exec(prefix) + (if s.index(s.len() as int - 1) == '1' { 1 } else { 0 }));
            assert(Str2Int(prefix) == Str2Int_exec(prefix));
            assert(Str2Int(s) == Str2Int_exec(s));
        }
    }
}

fn exp_exec(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 {
        1
    } else {
        x * exp_exec(x, y - 1)
    }
}

proof fn exp_exec_equiv(x: nat, y: nat)
    ensures Exp_int(x, y) == exp_exec(x, y),
    decreases y
{
    if y == 0 {
    } else {
        exp_exec_equiv(x, y - 1);
        proof {
            assert(Exp_int(x, y) == x * Exp_int(x, y - 1));
            assert(exp_exec(x, y) == x * exp_exec(x, y - 1));
            assert(Exp_int(x, y - 1) == exp_exec(x, y - 1));
            assert(Exp_int(x, y) == exp_exec(x, y));
        }
    }
}

fn nat_to_bits(n: nat) -> Vec<char>
    decreases n
{
    if n == 0 {
        Vec::<char>::new()
    } else {
        let mut v = nat_to_bits(n / 2);
        let bit = if n % 2 == 1 { '1' } else { '0' };
        v.push(bit);
        v
    }
}

proof fn nat_bits_inverse(n: nat)
    ensures Str2Int(nat_to_bits(n)@) == n,
    decreases n
{
    if n == 0 {
    } else {
        nat_bits_inverse(n / 2);
        proof {
            assert(Str2Int(nat_to_bits(n)@) == 2 * Str2Int(nat_to_bits(n / 2)@) + (if n % 2 == 1 { 1 } else { 0 }));
            assert(Str2Int(nat_to_bits(n / 2)@) == n / 2);
            assert(Str2Int(nat_to_bits(n)@) == n);
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let base = Str2Int_exec(sx@);
    let exp = Str2Int_exec(sy@);
    let m = Str2Int_exec(sz@);
    let pow = exp_exec(base, exp);
    let res_val = pow % m;
    let res_vec = nat_to_bits(res_val);
    proof {
        str2int_equiv(sx@);
        str2int_equiv(sy@);
        str2int_equiv(sz@);
        exp_exec_equiv(base, exp);
        nat_bits_inverse(res_val);
        assert(Str2Int(res_vec@) == res_val);
        assert(res_val == exp_exec(base, exp) % m);
        assert(exp_exec(base, exp) == Exp_int(Str2Int_exec(sx@), Str2Int_exec(sy@)));
        assert(Str2Int_exec(sx@) == Str2Int(sx@));
        assert(Str2Int_exec(sy@) == Str2Int(sy@));
        assert(exp_exec(base, exp) == Exp_int(Str2Int(sx@), Str2Int(sy@)));
        assert(m == Str2Int(sz@));
        assert(Str2Int(res_vec@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    res_vec
}
// </vc-code>

fn main() {}
}
