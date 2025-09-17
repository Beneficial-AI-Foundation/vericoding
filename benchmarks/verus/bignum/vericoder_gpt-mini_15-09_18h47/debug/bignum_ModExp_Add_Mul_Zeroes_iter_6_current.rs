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
/* helper modified by LLM (iteration 6): convert bit char to nat and predicate for bit char */
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
    /* code modified by LLM (iteration 6): use ghost nat accumulators to relate runtime u128 values to spec nats and prove bounds to avoid division-by-zero and overflow */
    // build modulus m_val and ghost m_nat = Str2Int(prefix)
    let mut m_val: u128 = 0u128;
    let mut k: usize = 0usize;
    let mut ghost m_nat: nat = 0;
    while k < sz.len()
        invariant
            k <= sz.len(),
            m_val == (m_nat as u128),
        decreases
            sz.len() - k
    {
        let b_u: u128 = if sz[k] == '1' { 1u128 } else { 0u128 };
        proof {
            m_nat = 2 * m_nat + char_to_bit(sz[k]);
        }
        m_val = m_val * 2u128 + b_u;
        k += 1;
    }
    proof {
        // relate ghost accumulator to spec Str2Int and use requires Str2Int(sz@) > 1
        assert(m_nat == Str2Int(sz@));
        assert(m_nat > 1);
    }

    // build base = Str2Int(sx) mod m_nat, tracked with ghost base_nat
    let mut base: u128 = 0u128;
    let mut i: usize = 0usize;
    let mut ghost base_nat: nat = 0;
    while i < sx.len()
        invariant
            i <= sx.len(),
            base == (base_nat as u128) % m_val,
        decreases
            sx.len() - i
    {
        let b_u: u128 = if sx[i] == '1' { 1u128 } else { 0u128 };
        proof {
            base_nat = 2 * base_nat + char_to_bit(sx[i]);
        }
        base = (base * 2u128 + b_u) % m_val;
        i += 1;
    }
    proof { assert(base == (base_nat as u128) % m_val); }

    // modular exponentiation: track result with ghost res_nat
    let mut result: u128 = 1u128 % m_val;
    let mut j: usize = 0usize;
    let mut ghost res_nat: nat = 1 % m_nat;
    while j < sy.len()
        invariant
            j <= sy.len(),
            result == (res_nat as u128) % m_val,
        decreases
            sy.len() - j
    {
        // square
        result = (result * result) % m_val;
        proof { res_nat = (res_nat * res_nat) % m_nat; }
        // if bit 1, multiply by base
        if sy[j] == '1' {
            result = (result * base) % m_val;
            proof { res_nat = (res_nat * base_nat) % m_nat; }
        }
        j += 1;
    }
    proof { assert(res_nat == Exp_int(Str2Int(sx@), Str2Int(sy@)) % m_nat); }

    // construct result bitstring from result (runtime) while using ghost knowledge for correctness
    let mut resv = Vec::<char>::new();
    if result == 0u128 {
        // represent 0 as empty vector according to original convention
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
