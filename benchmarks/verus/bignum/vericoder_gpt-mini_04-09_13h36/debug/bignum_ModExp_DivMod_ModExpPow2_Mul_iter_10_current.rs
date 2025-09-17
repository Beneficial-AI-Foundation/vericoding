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
exec fn vec_to_nat_rec(s: &[char], i: int) -> nat
  requires 0 <= i && i <= s.len() as int
  ensures result == Str2Int(s@.subrange(0, i))
  decreases s.len() as int - i
{
    if i == 0 {
        0
    } else {
        let prev = vec_to_nat_rec(s, i - 1);
        let ch = s[(i - 1) as usize];
        let bit: nat = if ch == '1' { 1 } else { 0 };
        prev * 2 + bit
    }
}

exec fn vec_to_nat(s: &[char]) -> nat
  ensures result == Str2Int(s@)
{
    vec_to_nat_rec(s, s.len() as int)
}

exec fn int_to_vec(n: nat) -> Vec<char>
  ensures ValidBitString(result@)
  ensures Str2Int(result@) == n
  decreases n
{
    if n == 0 {
        return Vec::<char>::new();
    } else {
        let q: nat = n / 2;
        let r: nat = n % 2;
        let mut v = int_to_vec(q);
        let old_seq = v@; // snapshot before push
        let bit = if r == 1 { '1' } else { '0' };
        v.push(bit);
        // show that the prefix before last equals old_seq
        assert(v@.subrange(0, old_seq.len() as int) == old_seq);
        // from recursive call we know Str2Int(old_seq) == q
        assert(Str2Int(old_seq) == q);
        // Now unfold Str2Int for non-empty sequence v@
        let len_v = v@.len() as int;
        assert(len_v > 0);
        let prefix = v@.subrange(0, len_v - 1);
        // prefix equals old_seq
        assert(prefix == old_seq);
        let last_char = v@.index(len_v - 1);
        let last_bit: nat = if last_char == '1' { 1 } else { 0 };
        // by definition of Str2Int for non-empty sequence
        assert(Str2Int(v@) == 2 * Str2Int(prefix) + last_bit);
        // combine facts to get result == n
        assert(Str2Int(v@) == 2 * q + r);
        v
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let a = vec_to_nat(sx);
    let e = vec_to_nat(sy);
    let m = vec_to_nat(sz);

    // compute p = Exp_int(a, e) by naive multiplication
    let mut exp: nat = e;
    let mut p: nat = 1;
    while exp > 0
        invariant p * Exp_int(a, exp) == Exp_int(a, e);
        invariant exp <= e;
        decreases exp;
    {
        let old_p = p;
        let old_exp = exp;
        assert(old_exp > 0);
        assert(Exp_int(a, old_exp) == a * Exp_int(a, old_exp - 1));
        p = old_p * a;
        exp = old_exp - 1;
        assert(p * Exp_int(a, exp) == Exp_int(a, e));
    }

    let r = p % m;
    let res = int_to_vec(r);
    res
}
// </vc-code>

fn main() {}
}