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
/* helper modified by LLM (iteration 3): predicate to check a char is a bit and converter to numeric bit */
spec fn is_bit(c: char) -> bool { c == '0' || c == '1' }
fn char_to_bit(c: char) -> nat { if c == '1' { 1 } else { 0 } }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): compute modulus, compute base as x mod m, perform left-to-right binary exponentiation over exponent bits, then build result bitstring */

    // compute m_val from sz (most-significant to least-significant)
    let mut m_val: u128 = 0u128;
    let mut k: usize = 0usize;
    while k < sz.len()
        invariant
            k <= sz.len(),
        decreases sz.len() - k
    {
        let b: u128 = if sz[k] == '1' { 1u128 } else { 0u128 };
        m_val = m_val * 2u128 + b;
        k += 1;
    }

    // compute base = x mod m (reduce as we build to keep values small)
    let mut base: u128 = 0u128;
    let mut i: usize = 0usize;
    while i < sx.len()
        invariant
            i <= sx.len(),
        decreases sx.len() - i
    {
        let b: u128 = if sx[i] == '1' { 1u128 } else { 0u128 };
        // m_val > 1 is a precondition; using modulo keeps base < m_val
        base = (base * 2u128 + b) % m_val;
        i += 1;
    }

    // left-to-right binary exponentiation using exponent bits from sy (MSB to LSB)
    let mut result: u128 = 1u128 % m_val;
    let mut j: usize = 0usize;
    while j < sy.len()
        invariant
            j <= sy.len(),
        decreases sy.len() - j
    {
        // square
        result = (result * result) % m_val;
        // if current exponent bit is 1, multiply by base
        if sy[j] == '1' {
            result = (result * base) % m_val;
        }
        j += 1;
    }

    // construct result bitstring (empty represents 0)
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
        decreases r
    {
        let c = if (r & 1u128) == 1u128 { '1' } else { '0' };
        rev.push(c);
        r = r >> 1;
    }

    // reverse to get MSB..LSB
    let mut idx: isize = rev.len() as isize - 1isize;
    while idx >= 0isize
        invariant
            idx >= -1isize,
        decreases idx + 1isize
    {
        resv.push(rev[idx as usize]);
        idx -= 1;
    }

    resv
}
// </vc-code>

fn main() {}
}
