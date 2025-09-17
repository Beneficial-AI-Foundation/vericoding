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
exec fn seq_to_nat(s: &[char]) -> nat
  requires ValidBitString(s@)
  ensures result == Str2Int(s@)
  decreases s@.len()
{
    if s.len() == 0 {
        0
    } else {
        let prefix = &s[0..s.len() - 1];
        let p = seq_to_nat(prefix);
        let bit = if s[s.len() - 1] == '1' { 1 } else { 0 };
        2 * p + bit
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
        let mut v = nat_to_bits(n / 2);
        let bit = if n % 2 == 1 { '1' } else { '0' };
        v.push(bit);
        v
    }
}

proof fn exp_add(a: nat, e1: nat, e2: nat)
  ensures Exp_int(a, e1 + e2) == Exp_int(a, e1) * Exp_int(a, e2)
  decreases e2
{
    if e2 == 0 {
        // e2 == 0: trivial, Exp_int(a, e1 + 0) == Exp_int(a, e1) == Exp_int(a, e1) * 1 == Exp_int(a, e1) * Exp_int(a, 0)
    } else {
        exp_add(a, e1, e2 - 1);
        // Exp_int(a, e1 + e2) = a * Exp_int(a, e1 + e2 - 1)
        // by IH, Exp_int(a, e1 + e2 - 1) = Exp_int(a, e1) * Exp_int(a, e2 - 1)
        // so Exp_int(a, e1 + e2) = a * (Exp_int(a, e1) * Exp_int(a, e2 - 1))
        // = Exp_int(a, e1) * (a * Exp_int(a, e2 - 1)) = Exp_int(a, e1) * Exp_int(a, e2)
    }
}

exec fn pow_mod(a: nat, e: nat, m: nat) -> nat
  requires m > 0
  ensures result == Exp_int(a, e) % m
  decreases e
{
    if e == 0 {
        1 % m
    } else {
        let t = pow_mod(a, e - 1, m);
        ((a % m) * t) % m
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x = seq_to_nat(sx);
    let y = seq_to_nat(sy);
    let m = seq_to_nat(sz);
    let r = pow_mod(x, y, m);
    let res = nat_to_bits(r);
    res
}
// </vc-code>

fn main() {}
}