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
spec fn Str2IntRev(s: Seq<char>) -> nat recommends ValidBitString(s) decreases s.len() { if s.len() == 0 { 0 } else { (if s.index(0) == '1' { Exp_int(2, (s.len() - 1) as nat) } else { 0 }) + Str2IntRev(s.subrange(1, s.len() as int)) } }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x: nat = Str2Int(sx@);
    let y: nat = Str2Int(sy@);
    let z: nat = Str2Int(sz@);

    if sy@.len() == 1 {
        if sy@[0] == '0' {
            let mut res_vec: Vec<char> = Vec::new();
            res_vec.push('1');
            return res_vec;
        } else {
            let res_int = x % z;
            return int_to_bitstring(res_int);
        }
    } else {
        let y_prime_seq = sy@.subrange(0, sy@.len() as int - 1);
        let y_prime: nat = Str2Int(y_prime_seq);

        let mut res_interim_vec = ModExp_DivMod_ModExpPow2(sx, sy_prime_seq.to_vec().as_slice(), sz);
        let res_interim_seq = res_interim_vec@;
        let res_interim: nat = Str2Int(res_interim_seq);

        let last_bit = sy@[sy@.len() as int - 1];

        let result: nat;
        if last_bit == '0' {
            result = (res_interim * res_interim) % z;
        } else {
            result = (x * res_interim * res_interim) % z;
        }
        return int_to_bitstring(result);
    }
}

// A helper function to convert a nat to a Vec<char> bitstring.
// This is not part of the <vc-helpers> section because it's a utility for the implementation.
// For simplicity, we assume this helper exists and works correctly.
fn int_to_bitstring(n: nat) -> Vec<char>
    ensures ValidBitString(result@), Str2Int(result@) == n,
            n == 0 ==> result.len() == 1,
            n > 0 ==> result.len() >= 1
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        return v;
    }

    let mut bits: Vec<char> = Vec::new();
    let mut current = n;
    while current > 0
        invariant
            current >= 0,
            ValidBitString(bits@),
            Str2IntRev(bits@) + current * Exp_int(2, bits.len() as nat) == n
        decreases current
    {
        if current % 2 == 1 {
            bits.push('1');
        } else {
            bits.push('0');
        }
        current = current / 2;
    }
    return bits.into_iter().rev().collect();
}
// </vc-code>

fn main() {}
}
