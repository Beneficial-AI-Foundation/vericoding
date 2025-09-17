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
/* helper modified by LLM (iteration 8): convert char to bit and predicate for bit char */
spec fn char_to_bit(c: char) -> nat { if c == '1' { 1 } else { 0 } }
spec fn is_bit(c: char) -> bool { c == '0' || c == '1' }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 8): add decreases and invariants to loops */
    let mut m_val: u128 = 0u128;
    let mut k: usize = 0usize;
    while k < sz.len()
        invariant
            k <= sz.len(),
        decreases
            sz.len() - k
    {
        let b: u128 = if sz[k] == '1' { 1u128 } else { 0u128 };
        m_val = m_val * 2u128 + b;
        k += 1;
    }

    if m_val <= 1u128 {
        return Vec::<char>::new();
    }

    let mut base: u128 = 0u128;
    let mut i: usize = 0usize;
    while i < sx.len()
        invariant
            i <= sx.len(),
        decreases
            sx.len() - i
    {
        let b: u128 = if sx[i] == '1' { 1u128 } else { 0u128 };
        base = (base * 2u128 + b) % m_val;
        i += 1;
    }

    let mut result: u128 = 1u128 % m_val;
    let mut j: usize = 0usize;
    while j < sy.len()
        invariant
            j <= sy.len(),
        decreases
            sy.len() - j
    {
        // square
        result = (result * result) % m_val;
        // if bit 1, multiply by base
        if sy[j] == '1' {
            result = (result * base) % m_val;
        }
        j += 1;
    }

    let mut resv = Vec::<char>::new();
    if result == 0u128 {
        return resv;
    }

    // collect LSB-first
    let mut rev = Vec::<char>::new();
    let mut r: u128 = result;
    while r > 0u128
        invariant
            r >= 0u128,
        decreases
            r
    {
        let bit = if (r & 1u128) == 1u128 { '1' } else { '0' };
        rev.push(bit);
        r = r >> 1;
    }

    // reverse to get MSB..LSB
    let mut p: usize = rev.len();
    while p > 0
        invariant
            p <= rev.len(),
        decreases
            p
    {
        p -= 1;
        resv.push(rev[p]);
    }

    resv
}
// </vc-code>

fn main() {}
}
