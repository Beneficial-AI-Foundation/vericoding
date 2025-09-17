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
        let v: Vec<char> = Vec::new();
        proof {
            assert(v@.len() == 0);
            assert(Str2Int(v@) == 0);
            assert(ValidBitString(v@));
        }
        v
    } else {
        let mut v = nat_to_bits(n / 2);
        let old = v.clone();
        let bit = if n % 2 == 1 { '1' } else { '0' };
        v.push(bit);
        proof {
            let res_seq = v@;
            let old_seq = old@;
            assert(res_seq.len() as int > 0);
            let last_idx: int = res_seq.len() as int - 1;
            assert(res_seq.index(last_idx) == bit);
            assert(res_seq.subrange(0, last_idx) == old_seq);
            assert(Str2Int(old_seq) == n / 2);
            assert(ValidBitString(old_seq));
            assert(Str2Int(res_seq) == 2 * Str2Int(old_seq) + (if bit == '1' { 1 } else { 0 }));
            assert((if bit == '1' { 1 } else { 0 }) == n % 2);
            assert(n == 2 * (n / 2) + n % 2);
            assert(Str2Int(res_seq) == n);
            assert(bit == '0' || bit == '1');
            assert(ValidBitString(res_seq));
        }
        v
    }
}

proof fn exp_add(a: nat, e1: nat, e2: nat)
  ensures Exp_int(a, e1 + e2) == Exp_int(a, e1) * Exp_int(a, e2)
  decreases e2
{
    if e2 == 0 {
        // base case
    } else {
        exp_add(a, e1, e2 - 1);
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
    proof {
        // Unfold seq_to_nat postconditions
        assert(x == Str2Int(sx@));
        assert(y == Str2Int(sy@));
        assert(m == Str2Int(sz@));
        // From precondition of ModExp we know Str2Int(sz@) > 1
        assert(Str2Int(sz@) > 1);
        assert(m > 0);
    }
    let r = pow_mod(x, y, m);
    let res = nat_to_bits(r);
    proof {
        // unfold pow_mod and nat_to_bits postconditions to get the desired equality
        assert(r == Exp_int(x, y) % m);
        assert(Str2Int(res@) == r);
        assert(Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
        assert(ValidBitString(res@));
    }
    res
}
// </vc-code>

fn main() {}
}