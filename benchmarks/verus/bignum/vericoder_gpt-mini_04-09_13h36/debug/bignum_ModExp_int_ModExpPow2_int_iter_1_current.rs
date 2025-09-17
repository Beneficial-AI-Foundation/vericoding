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
// <vc-helpers>

exec fn seq_to_nat(s: &[char]) -> (res: nat)
  requires ValidBitString(s@)
  ensures res == Str2Int(s@)
  decreases s.len()
{
    let mut i: usize = 0;
    let mut acc: nat = 0;
    while i < s.len() {
        invariant i <= s.len();
        invariant acc == Str2Int(s@.subrange(0, i as int));
        decreases s.len() - i;
        let c = s[i];
        let bitval: nat = if c == '1' { 1 } else { 0 };
        acc = acc * 2 + bitval;
        i = i + 1;
    }
    acc
}

exec fn pow_mod(base: nat, exp: nat, m: nat) -> (res: nat)
  requires m > 0
  ensures res == Exp_int(base, exp) % m
  decreases exp
{
    let mut i: nat = 0;
    let mut acc: nat = 1 % m;
    while i < exp {
        invariant i <= exp;
        invariant acc == Exp_int(base, i) % m;
        decreases exp - i;
        acc = (acc * base) % m;
        i = i + 1;
    }
    acc
}

exec fn nat_to_bitvec(n: nat) -> (v: Vec<char>)
  ensures ValidBitString(v@) && Str2Int(v@) == n
  decreases n
{
    if n == 0 {
        return Vec::<char>::new();
    } else {
        let mut prefix = nat_to_bitvec(n / 2);
        let last = if n % 2 == 1 { '1' } else { '0' };
        prefix.push(last);
        // proof that Str2Int(prefix@) == n:
        // by induction, Str2Int(prefix@) == 2*(n/2) + (n%2) == n
        prefix
    }
}

// </vc-helpers>
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int_ModExpPow2_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let base = seq_to_nat(sx);
    let exp = seq_to_nat(sy);
    let modulus = seq_to_nat(sz);
    let r = pow_mod(base, exp, modulus);
    let resvec = nat_to_bitvec(r);
    resvec
}
// </vc-code>

fn main() {}
}