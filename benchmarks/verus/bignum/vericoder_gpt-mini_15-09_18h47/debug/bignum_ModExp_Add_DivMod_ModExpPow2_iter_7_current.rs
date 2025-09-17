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

exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
{
  assume(false);
  return Vec::<char>::new();
}

exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
{
  assume(false);
  return (Vec::<char>::new(), Vec::<char>::new());
}

exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
{
  assume(false);
  return Vec::<char>::new();
}

// <vc-helpers>
/* helper modified by LLM (iteration 7): proves Exp_int(x,a)*Exp_int(x,b)=Exp_int(x,a+b) */
proof fn exp_add(x: nat, a: nat, b: nat)
    ensures
        Exp_int(x, a) * Exp_int(x, b) == Exp_int(x, a + b),
    decreases b
{
    if b == 0 {
        assert(Exp_int(x, b) == 1);
        assert(Exp_int(x, a) * Exp_int(x, b) == Exp_int(x, a));
        assert(Exp_int(x, a) == Exp_int(x, a + 0));
    } else {
        exp_add(x, a, (b - 1) as nat);
        assert(Exp_int(x, b) == x * Exp_int(x, (b - 1) as nat));
        assert(Exp_int(x, a) * Exp_int(x, b) == Exp_int(x, a) * x * Exp_int(x, (b - 1) as nat));
        assert(Exp_int(x, a) * x * Exp_int(x, (b - 1) as nat) == x * (Exp_int(x, a) * Exp_int(x, (b - 1) as nat)));
        assert(Exp_int(x, a) * Exp_int(x, (b - 1) as nat) == Exp_int(x, a + (b - 1) as nat));
        assert(x * Exp_int(x, a + (b - 1) as nat) == Exp_int(x, a + b));
        assert(Exp_int(x, a) * Exp_int(x, b) == Exp_int(x, a + b));
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
/* code modified by LLM (iteration 7): removed tracked usage, use usize/u128 for runtime arithmetic */
{
    // compute base from sx (runtime u128)
    let mut i: usize = 0;
    let mut base: u128 = 0;
    while i < sx.len()
        invariant
            i <= sx.len(),
        decreases sx.len() - i
    {
        let b = if sx[i] == '1' { 1u128 } else { 0u128 };
        base = base * 2 + b;
        i += 1;
    }

    // compute modulus m from sz
    let mut j: usize = 0;
    let mut m: u128 = 0;
    while j < sz.len()
        invariant
            j <= sz.len(),
        decreases sz.len() - j
    {
        let bb = if sz[j] == '1' { 1u128 } else { 0u128 };
        m = m * 2 + bb;
        j += 1;
    }

    // modular exponentiation using binary exponentiation over sy
    let mut k: usize = 0;
    let mut acc: u128 = if m == 0 { 0 } else { 1 % m };
    while k < sy.len()
        invariant
            k <= sy.len(),
        decreases sy.len() - k
    {
        // square
        if m != 0 { acc = (acc * acc) % m; }
        // multiply if bit is 1
        if sy[k] == '1' {
            if m != 0 { acc = (acc * base) % m; }
        }
        k += 1;
    }

    // build bit-vector result for acc modulo m
    let mut res = Vec::<char>::new();
    if acc == 0 {
        // represent zero as single '0'
        res.push('0');
        return res;
    }

    // find highest power of two greater than acc
    let mut pow: u128 = 1;
    while pow <= acc
        invariant
            pow >= 1,
        decreases (acc + 1) - pow
    {
        pow = pow * 2;
    }

    // emit bits from highest-1 down to 0
    while pow > 1
        invariant
            pow >= 1,
        decreases pow
    {
        pow = pow / 2;
        if acc >= pow {
            res.push('1');
            acc = acc - pow;
        } else {
            res.push('0');
        }
    }

    res
}

// </vc-code>

fn main() {}
}
