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
/* helper modified by LLM (iteration 4): define BitVal, SeqToNat, and prove MulMod_Compat using division/remainder */
spec fn BitVal(c: char) -> nat { if c == '1' { 1nat } else { 0nat } }
spec fn SeqToNat(s: Seq<char>) -> nat
    decreases s.len()
{
    Str2Int(s)
}
proof fn MulMod_Compat(a: nat, b: nat, m: nat)
    requires
        m > 0nat,
    ensures
        (a * b) % m == ((a % m) * (b % m)) % m,
{
    let r1 = a % m;
    let q1 = a / m;
    let r2 = b % m;
    let q2 = b / m;
    assert(a == q1 * m + r1);
    assert(b == q2 * m + r2);
    assert(a * b == (q1 * m + r1) * (q2 * m + r2));
    assert((q1 * m + r1) * (q2 * m + r2) == q1 * q2 * m * m + (q1 * r2 + q2 * r1) * m + r1 * r2);
    assert((a * b) % m == (r1 * r2) % m);
    assert(((a % m) * (b % m)) % m == (r1 * r2) % m);
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
    /* code modified by LLM (iteration 4): parse bitstrings into nat using nat literals and implement modular exponentiation */
    // parse modulus sz -> m
    let mut m: nat = 0nat;
    let mut i: usize = 0usize;
    let slen: usize = sz.len();
    while i < slen
        invariant
            i <= slen,
        decreases
            slen - i
    {
        let bit: nat = if sz[i] == '1' { 1nat } else { 0nat };
        m = 2nat * m + bit;
        i += 1;
    }

    // parse base sx -> base and reduce modulo m
    let mut base: nat = 0nat;
    let mut j: usize = 0usize;
    let bxlen: usize = sx.len();
    while j < bxlen
        invariant
            j <= bxlen,
        decreases
            bxlen - j
    {
        let bit: nat = if sx[j] == '1' { 1nat } else { 0nat };
        base = 2nat * base + bit;
        j += 1;
    }
    base = base % m;

    // modular exponentiation: process bits of sy from LSB to MSB
    let mut res: nat = 1nat % m;
    let mut k: usize = 0usize;
    let ylen: usize = sy.len();
    while k < ylen
        invariant
            k <= ylen,
        decreases
            ylen - k
    {
        // bit from LSB: sy[ylen-1-k]
        let bch: char = sy[ylen - 1 - k];
        if bch == '1' {
            res = (res * base) % m;
        }
        base = (base * base) % m;
        k += 1;
    }

    // convert result res to bit vector (MSB .. LSB, so last char is LSB)
    let mut bits = Vec::<char>::new();
    if res == 0nat {
        bits.push('0');
    } else {
        let mut r: nat = res;
        while r > 0nat
            invariant
                r >= 0nat,
            decreases
                r
        {
            if r % 2nat == 1nat {
                bits.push('1');
            } else {
                bits.push('0');
            }
            r = r / 2nat;
        }
        // bits currently LSB-first, reverse to make MSB-first (last = LSB)
        let mut p: usize = 0usize;
        let n: usize = bits.len();
        while p < n / 2
            invariant
                p <= n,
            decreases
                n - p
        {
            let q = n - 1 - p;
            let tmp = bits[p];
            bits[p] = bits[q];
            bits[q] = tmp;
            p += 1;
        }
    }

    return bits;
}

// </vc-code>

fn main() {}
}
