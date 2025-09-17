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
        // capture old v before push for use in proof
        let old = v.clone();
        let bit = if n % 2 == 1 { '1' } else { '0' };
        v.push(bit);
        proof {
            // Let res_seq be the sequence view of v after push
            let res_seq = v@;
            // res_seq has length > 0
            assert(res_seq.len() as int > 0);
            let last_idx: int = res_seq.len() as int - 1;
            // last element is the bit we pushed
            assert(res_seq.index(last_idx) == bit);
            // prefix is the original old@
            assert(res_seq.subrange(0, last_idx) == old@);
            // from recursive postcondition
            assert(Str2Int(old@) == n / 2);
            // by definition of Str2Int on non-empty sequence:
            // Str2Int(res_seq) == 2 * Str2Int(prefix) + bitVal
            assert(Str2Int(res_seq) == 2 * Str2Int(old@) + (if bit == '1' { 1 } else { 0 }));
            // relate bit to n % 2
            assert((if bit == '1' { 1 } else { 0 }) == n % 2);
            // arithmetic: n == 2*(n/2) + n%2
            assert(n == 2 * (n / 2) + n % 2);
            // combine to get Str2Int(res_seq) == n
            assert(Str2Int(res_seq) == n);
            // ValidBitString: old@ is valid by recursive postcondition; bit is '0' or '1'
            assert(old@.len() as int >= 0); // trivial to help prover
            assert(bit == '0' || bit == '1');
            // now conclude validity for res_seq
            assert(ValidBitString(old@));
            // for indices before last, res_seq equals old@, and last is bit in {'0','1'}
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
        // Exp_int(a, e1 + 0) == Exp_int(a, e1) == Exp_int(a, e1) * 1 == Exp_int(a, e1) * Exp_int(a, 0)
    } else {
        exp_add(a, e1, e2 - 1);
        // From definition: Exp_int(a, e1 + e2) = a * Exp_int(a, e1 + e2 - 1)
        // By IH: Exp_int(a, e1 + e2 - 1) = Exp_int(a, e1) * Exp_int(a, e2 - 1)
        // So Exp_int(a, e1 + e2) = a * (Exp_int(a, e1) * Exp_int(a, e2 - 1))
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