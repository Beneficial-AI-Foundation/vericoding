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
pub exec fn bits_to_nat(bs: &[char]) -> nat
  requires ValidBitString(bs@)
  ensures Str2Int(bs@) == result
  decreases bs.len()
{
    if bs.len() == 0 {
        0
    } else {
        let len_usize = bs.len() - 1;
        let last = bs[len_usize];
        let prefix = &bs[..len_usize];
        let acc = bits_to_nat(prefix);
        if last == '1' {
            2 * acc + 1
        } else {
            2 * acc
        }
    }
}

// Recursive helper that computes base^(Str2Int(sy@.subrange(0, i))) % modulus
pub exec fn modexp_idx(base: nat, modulus: nat, sy: &[char], i: int) -> nat
  requires 0 <= i && i <= sy.len() as int
  requires ValidBitString(sy@)
  requires modulus > 0
  ensures result == Exp_int(base, Str2Int(sy@.subrange(0, i))) % modulus
  decreases (sy.len() as int) - i
{
    if i == 0 {
        1 % modulus
    } else {
        let prev = modexp_idx(base, modulus, sy, i - 1);
        let b = sy[(i - 1) as usize];
        let tmp_sq = (prev * prev) % modulus;

        // prefix_val is the exponent corresponding to the previous prefix (length i-1)
        let prefix_val: nat = Str2Int(sy@.subrange(0, i - 1));
        // prev == Exp_int(base, prefix_val) % modulus
        assert(prev == Exp_int(base, prefix_val) % modulus);

        // tmp_sq == ((Exp_int(prefix_val) % modulus) * (Exp_int(prefix_val) % modulus)) % modulus
        assert(tmp_sq == ((Exp_int(base, prefix_val) % modulus) * (Exp_int(base, prefix_val) % modulus)) % modulus);
        // use modular multiplication lemma to move mod inside multiplication
        mod_mul_rem(Exp_int(base, prefix_val), Exp_int(base, prefix_val), modulus);
        assert(((Exp_int(base, prefix_val) % modulus) * (Exp_int(base, prefix_val) % modulus)) % modulus == (Exp_int(base, prefix_val) * Exp_int(base, prefix_val)) % modulus);
        // use exp_add to combine exponents
        exp_add(base, prefix_val, prefix_val);
        assert((Exp_int(base, prefix_val) * Exp_int(base, prefix_val)) % modulus == Exp_int(base, prefix_val + prefix_val) % modulus);
        assert(tmp_sq == Exp_int(base, prefix_val + prefix_val) % modulus);

        if b == '1' {
            // multiply by base once more
            mod_mul_rem(Exp_int(base, prefix_val + prefix_val), base, modulus);
            exp_add(base, prefix_val + prefix_val, 1);
            let tmp = (tmp_sq * (base % modulus)) % modulus;
            assert(tmp == Exp_int(base, prefix_val + prefix_val + 1) % modulus);
            tmp
        } else {
            tmp_sq
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let base: nat = bits_to_nat(sx);
    let modulus: nat = bits_to_nat(sz);
    assert(base == Str2Int(sx@));
    assert(modulus == Str2Int(sz@));

    let n: int = sy.len() as int;
    let result_nat: nat = modexp_idx(base, modulus, sy, n);

    assert(result_nat == Exp_int(base, Str2Int(sy@)) % modulus);

    let res_bits = nat_to_bits(result_nat);
    assert(ValidBitString(res_bits@));
    assert(Str2Int(res_bits@) == result_nat);
    assert(Str2Int(res_bits@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    res_bits
}
// </vc-code>

fn main() {}
}