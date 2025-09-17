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
exec fn seq_to_nat(s: &[char]) -> (res: nat)
  requires ValidBitString(s@)
  ensures res == Str2Int(s@)
  decreases s.len()
{
    if s.len() == 0 {
        return 0nat;
    } else {
        let last_idx = s.len() - 1;
        let last = s[last_idx];
        let pref = seq_to_nat(&s[..last_idx]);
        let bitval: nat = if last == '1' { 1nat } else { 0nat };
        return pref * 2nat + bitval;
    }
}

exec fn pow_mod(base: nat, exp: nat, m: nat) -> (res: nat)
  requires m > 0
  ensures res == Exp_int(base, exp) % m
  decreases exp
{
    if exp == 0nat {
        return 1nat % m;
    } else {
        let r = pow_mod(base, exp - 1nat, m);
        return (r * base) % m;
    }
}

exec fn nat_to_bitvec(n: nat) -> (v: Vec<char>)
  ensures ValidBitString(v@) && Str2Int(v@) == n
  decreases n
{
    if n == 0nat {
        return Vec::<char>::new();
    } else {
        let mut prefix = nat_to_bitvec(n / 2nat);
        let old_seq = prefix@;
        let last = if (n % 2nat) == 1nat { '1' } else { '0' };
        prefix.push(last);
        proof {
            // after push, the new sequence is old_seq ++ [last]
            assert(prefix@.len() as int == old_seq.len() as int + 1);
            assert(prefix@.subrange(0, prefix@.len() as int - 1) == old_seq);
            assert(prefix@.index(prefix@.len() as int - 1) == last);
            // by definition of Str2Int on sequences:
            assert(Str2Int(prefix@) == 2nat * Str2Int(prefix@.subrange(0, prefix@.len() as int - 1)) + (if last == '1' { 1nat } else { 0nat }));
            // replace subrange with old_seq (the prefix before push)
            assert(Str2Int(prefix@) == 2nat * Str2Int(old_seq) + (if last == '1' { 1nat } else { 0nat }));
            // by induction, Str2Int(old_seq) == n / 2
            assert(Str2Int(old_seq) == n / 2nat);
            // arithmetic: 2*(n/2) + (n%2) == n
            assert(2nat * (n / 2nat) + (n % 2nat) == n);
            // combine to get final equality
            assert(Str2Int(prefix@) == n);
        }
        prefix
    }
}
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
    proof {
        assert(base == Str2Int(sx@));
        assert(exp == Str2Int(sy@));
        assert(modulus == Str2Int(sz@));
        assert(r == Exp_int(base, exp) % modulus);
        assert(Str2Int(resvec@) == r);
        assert(ValidBitString(resvec@));
        assert(Str2Int(resvec@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    resvec
}
// </vc-code>

fn main() {}
}