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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

spec fn AllZero(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0'
}

// <vc-helpers>
use vstd::vec::Vec;

exec fn seq_to_nat(s: &[char]) -> (n: nat)
  ensures n == Str2Int(s@)
{
    // Compute Str2Int by iterating left-to-right (MSB-first)
    let mut i: nat = 0;
    let mut acc: nat = 0;
    while i < s.len()
        invariant i <= s.len()
        invariant acc == Str2Int(s@.subrange(0, i as int))
        decreases s.len() - i
    {
        let bit = if s[i] == '1' { 1 } else { 0 };
        acc = 2 * acc + bit;
        i = i + 1;
        proof {
            assert(acc == Str2Int(s@.subrange(0, i as int)));
        }
    }
    acc
}

lemma Str2Int_lt_pow2(s: Seq<char>)
  ensures Str2Int(s) < Exp_int(2, s.len() as nat)
  decreases s.len()
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0);
        assert(Exp_int(2, 0) == 1);
    } else {
        let last = s.index(s.len() as int - 1);
        let s0 = s.subrange(0, s.len() as int - 1);
        Str2Int_lt_pow2(s0);
        // Str2Int(s) = 2*Str2Int(s0) + bit, and Str2Int(s0) < 2^{len-1}
        assert(Str2Int(s) == 2 * Str2Int(s0) + (if last == '1' { 1 } else { 0 }));
        assert(2 * Str2Int(s0) < 2 * Exp_int(2, s0.len() as nat));
        assert(2 * Exp_int(2, s0.len() as nat) == Exp_int(2, s.len() as nat));
        // since bit <= 1, combine to get Str2Int(s) < 2^{len}
        assert(Str2Int(s) < Exp_int(2, s.len() as nat));
    }
}

exec fn pow2(e: nat) -> (r: nat)
  ensures r == Exp_int(2, e)
{
    let mut i: nat = 0;
    let mut acc: nat = 1;
    while i < e
        invariant i <= e
        invariant acc == Exp_int(2, i)
        decreases e - i
    {
        acc = acc * 2;
        i = i + 1;
        proof { assert(acc == Exp_int(2, i)); }
    }
    acc
}

exec fn nat_to_bits_fixed(n: nat, len: nat) -> (res: Vec<char>)
  requires n < Exp_int(2, len)
  ensures res.len() == len
  ensures Str2Int(res@) == n
  ensures ValidBitString(res@)
{
    let mut res: Vec<char> = Vec::new();
    let mut i: nat = 0;
    let mut acc: nat = 0; // numeric value of bits in res
    let mut rem: nat = n; // remaining value = n - acc * 2^{len - i}
    // initial invariants
    proof {
        assert(acc == 0);
        assert(res.len() == 0);
        assert(rem == n);
        assert(rem < Exp_int(2, len));
    }
    while i < len
        invariant i <= len
        invariant res.len() == i
        invariant acc == Str2Int(res@)
        invariant rem == n - acc * Exp_int(2, len - i)
        invariant rem < Exp_int(2, len - i)
        decreases len - i
    {
        let pow = pow2(len - i - 1);
        if rem >= pow {
            res.push('1');
            acc = acc * 2 + 1;
            rem = rem - pow;
        } else {
            res.push('0');
            acc = acc * 2;
        }
        i = i + 1;
        proof {
            // After pushing the bit, update Str2Int(res@) relation
            // Let old_acc be acc_old, old_res be previous sequence.
            // Then new Str2Int = 2 * old_acc + bit, which matches acc.
            assert(acc == Str2Int(res@));
            // And rem maintained as n - acc * 2^{len - i}
            assert(rem < Exp_int(2, len - i));
        }
    }
    // At the end, i == len, rem < 1 so rem == 0 and acc == n
    proof {
        assert(res.len() == len);
        assert(rem < Exp_int(2, 0));
        assert(rem == 0);
        assert(acc == n);
        assert(Str2Int(res@) == acc);
    }
    res
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
{
    let x = seq_to_nat(sx);
    let y = seq_to_nat(sy);
    let m = seq_to_nat(sz);

    // simple repeated-multiplication modular exponentiation:
    let mut i: nat = 0;
    let mut acc: nat = 1 % m;
    while i < y
        invariant i <= y
        invariant acc == Exp_int(x, i) % m
        decreases y - i
    {
        acc = (acc * x) % m;
        i = i + 1;
        proof { assert(acc == Exp_int(x, i) % m); }
    }

    // prove acc < 2^{len(sz)} to be able to encode in len(sz) bits
    proof {
        assert(m == Str2Int(sz@));
        // acc is a modulo result, so acc < m
        assert(acc < m);
        // Str2Int(sz) < 2^{len}
        Str2Int_lt_pow2(sz@);
        assert(m < Exp_int(2, sz.len()));
        assert(acc < Exp_int(2, sz.len()));
    }

    let res_vec = nat_to_bits_fixed(acc, sz.len());
    res_vec
}
// </vc-code>

fn main() {}
}