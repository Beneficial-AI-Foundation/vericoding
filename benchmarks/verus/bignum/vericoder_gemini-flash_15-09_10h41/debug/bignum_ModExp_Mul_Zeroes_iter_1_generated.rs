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
proof fn lemma_subrange_len(s: Seq<char>, start: int, end: int)
    requires
        0 <= start,
        start <= end,
        end <= s.len()
    ensures
        s.subrange(start, end).len() == end - start
    {}

proof fn lemma_Str2Int_non_negative(s: Seq<char>)
    requires
        ValidBitString(s)
    ensures
        Str2Int(s) >= 0
    {}

proof fn lemma_Str2Int_concat(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1'
    ensures
        Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1 } else { 0 })
    {}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let sy_len = sy.len();
    if sy_len == 0 {
        let mut res = Vec::new();
        res.push('1');
        return res;
    } else if sy_len == 1 {
        let first_char = sy[0];
        if first_char == '0' {
            let mut res = Vec::new();
            res.push('1');
            return res;
        } else {
            return Vec::from(sx);
        }
    }

    let half_sy_len_int = sy_len as int / 2;
    let half_sy_len_nat = half_sy_len_int as nat;

    let sy_half_1_seq = sy@.subrange(0, half_sy_len_int);
    let sy_half_2_seq = sy@.subrange(half_sy_len_int, sy_len as int);

    let r1 = ModExp_Mul_Zeroes(sx, &Vec::from_seq(sy_half_1_seq), sz);
    let r2 = ModExp_Mul_Zeroes(sx, &Vec::from_seq(sy_half_2_seq), sz);

    let modulus = Str2Int(sz@);
    let r1_val = Str2Int(r1@);
    let r2_val = Str2Int(r2@);

    let prod_val = (r1_val * r2_val) % modulus;

    let mut bit_string: Vec<char> = Vec::new();
    let mut temp_prod = prod_val;

    proof {
        lemma_Str2Int_non_negative(r1@);
        lemma_Str2Int_non_negative(r2@);
        assert (r1_val >= 0 && r2_val >= 0); // For product calculation
    }

    if temp_prod == 0 {
        bit_string.push('0');
    } else {
        while temp_prod > 0
            invariant
                ValidBitString(bit_string@),
                temp_prod >= 0,
                // This invariant ensures that the number represented by 'bit_string' would be 'prod_val' if 'temp_prod' reaches 0,
                // considering the bits are appended in reverse order.
                // We need a more rigorous invariant for Str2Int, but for now we'll focus on termination and correctness of bits.
                prod_val == if bit_string.len() == 0 { temp_prod } else { Str2Int(bit_string@) + Exp_int(2, bit_string.len() as nat) * temp_prod },
            decreases temp_prod
        {
            let rem = temp_prod % 2;
            if rem == 1 {
                bit_string.push('1');
            } else {
                bit_string.push('0');
            }
            temp_prod = temp_prod / 2;
        }
    }

    bit_string.reverse();
    return bit_string;
}
// </vc-code>

fn main() {}
}
