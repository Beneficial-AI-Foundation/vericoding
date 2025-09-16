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
spec fn all_fits_in_u64(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> bool
{
    ValidBitString(sx) && ValidBitString(sy) && ValidBitString(sz) &&
    sy.len() > 0 && Str2Int(sz) > 1 &&
    Str2Int(sx) < 18446744073709551616 &&
    Str2Int(sy) < 18446744073709551616 &&
    Str2Int(sz) < 18446744073709551616
}

/* helper modified by LLM (iteration 5): Added get_bits helper */
exec fn get_bits(s: Seq<char>) -> (bits: Seq<u64>)
    requires
        ValidBitString(s),
    ensures
        bits.len() * 64 + s.len() % 64 <= s.len(),
        forall |i: int| 0 <= i < bits.len() ==> bits.index(i) < 18446744073709551616,
    decreases s.len(),
{
    let mut bits = Seq::empty();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            bits.len() == (i / 64).downto(0),
        decreases s.len() - i,
    {
        let mut val: u64 = 0;
        let mut j = 0;
        while j < 64 && i + j < s.len()
            invariant
                0 <= j <= 64,
                i + j <= s.len(),
                val < 18446744073709551616,
            decreases 64 - j,
        {
            if s.index(i + j as int) == '1' {
                val = val | (1u64 << j);
            }
            j = j + 1;
        }
        bits = bits.push(val);
        i = i + 64;
    }
    bits
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation by removing spec fn from exec body */
{
    proof {
        assert(all_fits_in_u64(sx@, sy@, sz@));
    }
    let x_bits = get_bits(sx@);
    let y_bits = get_bits(sy@);
    let z_bits = get_bits(sz@);
    let mut result = 1u64;
    let mut b = str_to_u64(sx@);
    let mut e = 0;
    while e < y_bits.len()
        invariant
            0 <= e <= y_bits.len(),
            b < 18446744073709551616,
            result < 18446744073709551616,
        decreases y_bits.len() - e,
    {
        let word = y_bits[e];
        let mut j = 0;
        while j < 64
            invariant
                0 <= j <= 64,
                b < 18446744073709551616,
                result < 18446744073709551616,
            decreases 64 - j,
        {
            if (word & (1u64 << j)) != 0 {
                result = (((result as i128 * b as i128) % str_to_u64(sz@) as i128) as u64);
            }
            b = (((b as i128 * b as i128) % str_to_u64(sz@) as i128) as u64);
            j = j + 1;
        }
        e = e + 1;
    }
    let res = nat_to_binary(result);
    res
}
// </vc-code>

fn main() {}
}
