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

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): perform binary addition using int arithmetic and safe loop invariants */
    let mut i1: int = s1.len() as int;
    let mut i2: int = s2.len() as int;
    let mut carry: int = 0;
    let mut tmp = Vec::<char>::new();
    while i1 > 0 || i2 > 0
        invariant
            0 <= i1 && i1 <= s1.len() as int,
            0 <= i2 && i2 <= s2.len() as int,
        decreases i1 + i2
    {
        let b1: int = if i1 > 0 { if s1[(i1 - 1) as usize] == '1' { 1 } else { 0 } } else { 0 };
        let b2: int = if i2 > 0 { if s2[(i2 - 1) as usize] == '1' { 1 } else { 0 } } else { 0 };
        if i1 > 0 { i1 -= 1; }
        if i2 > 0 { i2 -= 1; }
        let sum: int = b1 + b2 + carry;
        if sum % 2 == 1 {
            tmp.push('1');
        } else {
            tmp.push('0');
        }
        carry = sum / 2;
    }
    if carry == 1 {
        tmp.push('1');
    }
    let mut res = Vec::<char>::new();
    let mut j: usize = tmp.len();
    while j > 0
        invariant
            j <= tmp.len(),
        decreases j
    {
        j -= 1;
        res.push(tmp[j]);
    }
    res
}
// </vc-code>

// <vc-spec>
exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): compute modulus, base mod, and repeated-squaring exponentiation with loop invariants linking to Str2Int */
    // compute m from sz, maintain invariant relating m to prefix Str2Int
    let mut m: usize = 0;
    let mut idx: usize = 0;
    while idx < sz.len()
        invariant
            idx <= sz.len(),
            (m as nat) == Str2Int(sz@.subrange(0, idx as int)),
        decreases sz.len() - idx
    {
        let bit = if sz[idx] == '1' { 1usize } else { 0usize };
        m = 2 * m + bit;
        idx += 1;
    }
    proof { assert((m as nat) == Str2Int(sz@)); }
    // m > 1 is ensured by precondition

    // compute base_mod = Str2Int(sx@) % m with invariant
    let mut base_mod: usize = 0;
    let mut i: usize = 0;
    while i < sx.len()
        invariant
            i <= sx.len(),
            (base_mod as nat) == Str2Int(sx@.subrange(0, i as int)) % (m as nat),
        decreases sx.len() - i
    {
        let bit = if sx[i] == '1' { 1usize } else { 0usize };
        base_mod = (2 * base_mod + bit) % m;
        i += 1;
    }
    proof { assert((base_mod as nat) == Str2Int(sx@) % (m as nat)); }

    // detect zero exponent (sy == 0)
    let mut is_zero: bool = true;
    let mut k: usize = 0;
    while k < sy.len()
        invariant
            k <= sy.len(),
            is_zero ==> (Str2Int(sy@.subrange(0, k as int)) == 0),
        decreases sy.len() - k
    {
        if sy[k] == '1' {
            is_zero = false;
            // break by advancing to end
            k = sy.len();
        } else {
            k += 1;
        }
    }

    // compute result integer modulo m
    let mut result_int: usize;
    if is_zero {
        // exponent 0 -> result = 1 mod m
        result_int = 1 % m;
    } else {
        // exponent is 2^n; repeated squaring n times
        let mut r: usize = base_mod % m;
        // sy.len() == n+1 per requires, so number of squarings is sy.len()-1
        let mut t: usize = if sy.len() == 0 { 0 } else { sy.len() - 1 };
        while t > 0
            invariant
                t <= (sy.len() - 1),
            decreases t
        {
            r = (r * r) % m;
            t -= 1;
        }
        result_int = r % m;
    }

    // convert result_int to bit vector (MSB first)
    let mut tmp = Vec::<char>::new();
    if result_int == 0 {
        tmp.push('0');
    } else {
        let mut v: usize = result_int;
        while v > 0
            invariant
                v >= 0,
            decreases v
        {
            let bit = if v % 2 == 1 { '1' } else { '0' };
            tmp.push(bit);
            v = v / 2;
        }
    }
    let mut res = Vec::<char>::new();
    let mut j: usize = tmp.len();
    while j > 0
        invariant
            j <= tmp.len(),
        decreases j
    {
        j -= 1;
        res.push(tmp[j]);
    }

    res
}
// </vc-code>

fn main() {}
}


