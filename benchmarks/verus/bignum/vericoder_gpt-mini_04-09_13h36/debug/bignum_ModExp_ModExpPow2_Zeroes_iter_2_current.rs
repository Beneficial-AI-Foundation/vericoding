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
  decreases s.len()
{
    let mut res: nat = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant 0 <= i && i <= s.len()
        invariant res == Str2Int(s@.subrange(0, i as int))
        decreases s.len() - i
    {
        let c = s[i];
        let bit: nat = if c == '1' { 1 } else { 0 };
        // update res: new_res = 2 * res + bit
        res = 2 * res + bit;
        i += 1;
    }
    return res;
}

exec fn nat_to_bits(n: nat) -> Vec<char>
  ensures ValidBitString(result@)
  ensures Str2Int(result@) == n
  decreases n
{
    if n == 0 {
        return Vec::<char>::new();
    } else {
        let mut v = nat_to_bits(n / 2);
        let bitc: char = if n % 2 == 1 { '1' } else { '0' };
        let old_seq = v@;
        v.push(bitc);
        let new_seq = v@;
        // prove ValidBitString
        assert(forall |i: int| 0 <= i && i < new_seq.len() as int ==> (new_seq.index(i) == '0' || new_seq.index(i) == '1'));
        // Now prove Str2Int(new_seq) == n
        let len_new = new_seq.len() as int;
        // last bit value
        let last_bit_val: nat = if new_seq.index(len_new - 1) == '1' { 1 } else { 0 };
        // by definition Str2Int(new_seq) = 2 * Str2Int(new_seq.subrange(0, len_new-1)) + last_bit_val
        // and new_seq.subrange(0, len_new-1) == old_seq, and by IH Str2Int(old_seq) == n/2
        assert(new_seq.subrange(0, len_new - 1) == old_seq);
        assert(Str2Int(old_seq) == n / 2);
        assert(Str2Int(new_seq) == 2 * Str2Int(new_seq.subrange(0, len_new - 1)) + last_bit_val);
        assert(last_bit_val == n % 2);
        assert(n == 2 * (n / 2) + (n % 2));
        // combine equalities
        // Str2Int(new_seq) == 2 * Str2Int(old_seq) + (n % 2) == 2*(n/2) + n%2 == n
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
        // t == Exp_int(b, e-1) % m by IH
        let res = (b % m) * t % m;
        // by IH and arithmetic, res == Exp_int(b,e) % m because Exp_int(b,e) = b * Exp_int(b,e-1)
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
    // modulus precondition ensures m > 1
    let base = b % m;
    let r = mod_pow(base, e, m);
    let v = nat_to_bits(r);
    return v;
}
// </vc-code>

fn main() {}
}