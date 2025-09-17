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
/* helper modified by LLM (iteration 4): spec version of Str2Int to avoid ambiguous integer literals */
spec fn Str2Int_exec(s: Seq<char>) -> nat
recommends ValidBitString(s)
decreases s.len()
{
    if s.len() == 0 { 0 } else { 2 * Str2Int_exec(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1 } else { 0 }) }
}

/* helper modified by LLM (iteration 4): proof relating Str2Int to Str2Int_exec */
proof fn str2int_equiv(s: Seq<char>)
    requires ValidBitString(s),
    ensures Str2Int(s) == Str2Int_exec(s),
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        let prefix = s.subrange(0, s.len() as int - 1);
        str2int_equiv(prefix);
        proof {
            assert(Str2Int(s) == 2 * Str2Int(prefix) + (if s.index(s.len() as int - 1) == '1' { 1 } else { 0 }));
            assert(Str2Int_exec(s) == 2 * Str2Int_exec(prefix) + (if s.index(s.len() as int - 1) == '1' { 1 } else { 0 }));
            assert(Str2Int(prefix) == Str2Int_exec(prefix));
            assert(Str2Int(s) == Str2Int_exec(s));
        }
    }
}

/* helper modified by LLM (iteration 4): executable exponentiation over nat */
fn exp_exec(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 {
        1
    } else {
        let y1: nat = (y - 1) as nat;
        x * exp_exec(x, y1)
    }
}

/* helper modified by LLM (iteration 4): proof relating Exp_int to exp_exec */
proof fn exp_exec_equiv(x: nat, y: nat)
    ensures Exp_int(x, y) == exp_exec(x, y),
    decreases y
{
    if y == 0 {
    } else {
        let y1: nat = (y - 1) as nat;
        exp_exec_equiv(x, y1);
        proof {
            assert(Exp_int(x, y) == x * Exp_int(x, y1));
            assert(exp_exec(x, y) == x * exp_exec(x, y1));
            assert(Exp_int(x, y1) == exp_exec(x, y1));
            assert(Exp_int(x, y) == exp_exec(x, y));
        }
    }
}

/* helper modified by LLM (iteration 4): convert nat to bit-vector (LSB last pushed) */
fn nat_to_bits(n: nat) -> Vec<char>
    decreases n
{
    if n == 0 {
        Vec::<char>::new()
    } else {
        let m: nat = n / 2;
        let mut v = nat_to_bits(m);
        let bit = if n % 2 == 1 { '1' } else { '0' };
        v.push(bit);
        v
    }
}

/* helper modified by LLM (iteration 4): proof that nat_to_bits inverts Str2Int */
proof fn nat_bits_inverse(n: nat)
    ensures Str2Int(nat_to_bits(n)@) == n,
    decreases n
{
    if n == 0 {
    } else {
        let m: nat = n / 2;
        nat_bits_inverse(m);
        proof {
            assert(Str2Int(nat_to_bits(n)@) == 2 * Str2Int(nat_to_bits(m)@) + (if n % 2 == 1 { 1 } else { 0 }));
            assert(Str2Int(nat_to_bits(m)@) == m);
            assert(Str2Int(nat_to_bits(n)@) == n);
        }
    }
}

// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): compute numeric values using u128 and perform modular exponentiation, converting back to bit-vector */
    let mut base_u128: u128 = 0u128;
    let mut i = 0usize;
    while i < sx.len() {
        let bit = if sx[i] == '1' { 1u128 } else { 0u128 };
        base_u128 = base_u128 * 2u128 + bit;
        i += 1usize;
    }

    let mut exp_u128: u128 = 0u128;
    let mut j = 0usize;
    while j < sy.len() {
        let bit = if sy[j] == '1' { 1u128 } else { 0u128 };
        exp_u128 = exp_u128 * 2u128 + bit;
        j += 1usize;
    }

    let mut m_u128: u128 = 0u128;
    let mut k = 0usize;
    while k < sz.len() {
        let bit = if sz[k] == '1' { 1u128 } else { 0u128 };
        m_u128 = m_u128 * 2u128 + bit;
        k += 1usize;
    }

    // modular exponentiation (binary exp) on u128 values
    let mut result_u128: u128 = 1u128 % m_u128;
    let mut base_mod: u128 = base_u128 % m_u128;
    let mut e = exp_u128;
    while e > 0u128 {
        if e % 2u128 == 1u128 {
            result_u128 = (result_u128 * base_mod) % m_u128;
        }
        base_mod = (base_mod * base_mod) % m_u128;
        e = e / 2u128;
    }

    // convert result_u128 to Vec<char> with MSB..LSB ordering (last element is LSB)
    let mut res = Vec::<char>::new();
    if result_u128 == 0u128 {
        // empty vector represents 0
    } else {
        // collect bits LSB-first then reverse to MSB..LSB
        let mut tmp = Vec::<char>::new();
        let mut t = result_u128;
        while t > 0u128 {
            let b = if t % 2u128 == 1u128 { '1' } else { '0' };
            tmp.push(b);
            t = t / 2u128;
        }
        // reverse tmp into res
        let mut p = tmp.len();
        while p > 0usize {
            p -= 1usize;
            res.push(tmp[p]);
        }
    }
    res
}

// </vc-code>

fn main() {}
}
