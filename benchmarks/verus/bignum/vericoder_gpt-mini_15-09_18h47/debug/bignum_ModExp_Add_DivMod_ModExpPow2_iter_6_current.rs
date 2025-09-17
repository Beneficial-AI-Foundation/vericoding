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
/* helper modified by LLM (iteration 6): proves Exp_int(x,a)*Exp_int(x,b)=Exp_int(x,a+b) */
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
/* code modified by LLM (iteration 6): implement modular exponentiation with tracked variables and proofs */
{
    let mut i: int = tracked(0);
    let mut base: nat = tracked(0);
    while i < sx.len() as int
        invariant
            0 <= i && i <= sx.len() as int,
            base == Str2Int(sx@.subrange(0, i)),
        decreases sx.len() as int - i
    {
        let b = if sx.index(i) == '1' { 1nat } else { 0nat };
        base = 2 * base + b;
        i = i + 1;
    }

    let mut j: int = tracked(0);
    let mut m: nat = tracked(0);
    while j < sz.len() as int
        invariant
            0 <= j && j <= sz.len() as int,
            m == Str2Int(sz@.subrange(0, j)),
        decreases sz.len() as int - j
    {
        let bb = if sz.index(j) == '1' { 1nat } else { 0nat };
        m = 2 * m + bb;
        j = j + 1;
    }

    // m > 1 is guaranteed by precondition
    let mut k: int = tracked(0);
    let mut acc: nat = tracked(1 % m);
    while k < sy.len() as int
        invariant
            0 <= k && k <= sy.len() as int,
            acc == Exp_int(base, Str2Int(sy@.subrange(0, k))) % m,
        decreases sy.len() as int - k
    {
        // square
        acc = (acc * acc) % m;
        // multiply if bit is 1
        if sy.index(k) == '1' {
            acc = (acc * base) % m;
        }

        proof {
            let pre = Str2Int(sy@.subrange(0, k));
            // show square corresponds to doubling exponent
            exp_add(base, pre, pre);
            assert((Exp_int(base, pre) * Exp_int(base, pre)) % m == Exp_int(base, pre + pre) % m);
            if sy.index(k) == '1' {
                // show multiply corresponds to adding 1
                exp_add(base, pre + pre, 1);
                assert((Exp_int(base, pre + pre) * base) % m == Exp_int(base, pre + pre + 1) % m);
            }
        }

        k = k + 1;
    }

    if acc == 0 {
        return Vec::<char>::new();
    }

    let mut pow: nat = tracked(1);
    while pow <= acc
        invariant
            pow >= 1,
        decreases (acc + 1) - pow
    {
        pow = pow * 2;
    }

    let mut d: nat = tracked(pow);
    let mut rem: nat = tracked(acc);
    let mut res = Vec::<char>::new();
    while d > 1
        invariant
            rem < pow,
            Str2Int(res@) * d + rem == acc,
        decreases d
    {
        d = d / 2;
        if rem >= d {
            res.push('1');
            rem = rem - d;
        } else {
            res.push('0');
        }
    }

    proof {
        assert(rem == 0);
        assert(Str2Int(res@) == acc);
    }

    res
}
// </vc-code>

fn main() {}
}
