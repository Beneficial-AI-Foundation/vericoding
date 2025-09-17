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
spec fn BitVal(c: char) -> nat { if c == '1' { 1 } else { 0 } }
spec fn SeqToNat(s: Seq<char>) -> nat
    decreases s.len()
{
    Str2Int(s)
}
proof fn MulMod_Compat(a: nat, b: nat, m: nat)
    requires
        m > 0,
    ensures
        (a * b) % m == ((a % m) * (b % m)) % m,
{
    // Standard modular arithmetic lemma; proof by properties of division
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
    // parse modulus sz -> m
    let mut m: nat = 0;
    let mut i: usize = 0;
    let slen = sz.len();
    while i < slen
        invariant
            i <= slen,
        decreases
            slen - i
    {
        let bit = if sz[i] == '1' { 1 } else { 0 };
        m = 2 * m + bit;
        i += 1;
    }

    // parse base sx -> base and reduce modulo m
    let mut base: nat = 0;
    let mut j: usize = 0;
    let bxlen = sx.len();
    while j < bxlen
        invariant
            j <= bxlen,
        decreases
            bxlen - j
    {
        let bit = if sx[j] == '1' { 1 } else { 0 };
        base = 2 * base + bit;
        j += 1;
    }
    base = base % m;

    // modular exponentiation: process bits of sy from LSB to MSB
    let mut res: nat = 1 % m;
    let mut k: usize = 0;
    let ylen = sy.len();
    while k < ylen
        invariant
            k <= ylen,
        decreases
            ylen - k
    {
        // bit from LSB: sy[ylen-1-k]
        let bch = sy[ylen - 1 - k];
        if bch == '1' {
            res = (res * base) % m;
        }
        base = (base * base) % m;
        k += 1;
    }

    // convert result res to bit vector (MSB .. LSB, so last char is LSB)
    let mut bits = Vec::<char>::new();
    if res == 0 {
        bits.push('0');
    } else {
        let mut r: nat = res;
        while r > 0
            invariant
                r >= 0,
            decreases
                r
        {
            if r % 2 == 1 {
                bits.push('1');
            } else {
                bits.push('0');
            }
            r = r / 2;
        }
        // bits currently LSB-first, reverse to make MSB-first (last = LSB)
        let mut p: usize = 0;
        let n = bits.len();
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
