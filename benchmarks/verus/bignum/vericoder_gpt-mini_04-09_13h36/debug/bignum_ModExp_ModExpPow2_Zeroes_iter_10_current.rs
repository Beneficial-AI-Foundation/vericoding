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
exec fn slice_to_nat(s: &[char]) -> nat
  requires ValidBitString(s@)
  ensures result == Str2Int(s@)
  decreases s@.len()
{
    let len_n: nat = s@.len();
    if len_n == 0 {
        return 0;
    } else {
        let last = s[len_n as usize - 1];
        let prefix = &s[..(len_n as usize - 1)];
        let res_prefix = slice_to_nat(prefix);
        let bit: nat = if last == '1' { 1 } else { 0 };
        return 2 * res_prefix + bit;
    }
}

exec fn nat_to_bits(n: nat) -> Vec<char>
  ensures ValidBitString(result@)
  ensures Str2Int(result@) == n
  decreases n
{
    if n == 0 {
        let v = Vec::<char>::new();
        proof {
            // empty sequence has integer value 0 and is a valid bitstring
            assert(Str2Int(v@) == 0);
            assert(forall |i: int| 0 <= i && i < v@.len() as int ==> (v@.index(i) == '0' || v@.index(i) == '1'));
        }
        return v;
    } else {
        let mut v = nat_to_bits(n / 2);
        let old_seq = v@;
        let bitc: char = if n % 2 == 1 { '1' } else { '0' };
        v.push(bitc);
        let new_seq = v@;
        proof {
            // valid bitstring: old_seq valid by IH, appended bit is '0' or '1'
            assert(forall |i: int| 0 <= i && i < old_seq.len() as int ==> (old_seq.index(i) == '0' || old_seq.index(i) == '1'));
            assert(bitc == '0' || bitc == '1');
            assert(forall |i: int| 0 <= i && i < new_seq.len() as int ==> (new_seq.index(i) == '0' || new_seq.index(i) == '1'));

            // relate new_seq to old_seq
            let len_new = new_seq.len() as int;
            assert(len_new >= 1);
            assert(new_seq.subrange(0, len_new - 1) == old_seq);

            // compute last bit numeric value
            let last_bit_val: nat = if new_seq.index(len_new - 1) == '1' { 1 } else { 0 };
            // IH: Str2Int(old_seq) == n / 2
            assert(Str2Int(old_seq) == n / 2);
            // definition of Str2Int for non-empty sequence
            assert(Str2Int(new_seq) == 2 * Str2Int(new_seq.subrange(0, len_new - 1)) + last_bit_val);
            // relate last bit to n % 2
            assert(new_seq.index(len_new - 1) == bitc);
            assert(last_bit_val == (if bitc == '1' { 1 } else { 0 }));
            assert(last_bit_val == n % 2);
            // arithmetic identity
            assert(n == 2 * (n / 2) + (n % 2));
            // conclude
            assert(Str2Int(new_seq) == n);
        }
        return v;
    }
}

exec fn mod_pow(b: nat, e: nat, m: nat) -> nat
  requires m > 1
  ensures result == Exp_int(b, e) % m
  decreases e
{
    if e == 0 {
        return 1 % m;
    } else {
        let t = mod_pow(b, e - 1, m);
        let res = (b % m) * t % m;
        return res;
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let m = slice_to_nat(sz);
    let b = slice_to_nat(sx);
    let e = slice_to_nat(sy);
    let r = mod_pow(b, e, m);
    let v = nat_to_bits(r);
    return v;
}
// </vc-code>

fn main() {}
}