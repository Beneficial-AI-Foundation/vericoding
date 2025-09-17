use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
spec fn Pow2(n: nat) -> nat {
    if n == 0 { 1 } else { 2 * Pow2(n - 1) }
}

proof fn Pow2_succ(n: nat)
    ensures Pow2(n + 1) == 2 * Pow2(n)
{
    if n == 0 {
    } else {
        Pow2_succ(n - 1);
    }
}

exec fn seq_to_nat(s: &[char]) -> nat
  requires ValidBitString(s@)
  ensures result == Str2Int(s@)
{
    let mut i: usize = 0usize;
    let mut acc: nat = 0;
    while i < s.len() {
        invariant 0usize <= i;
        invariant i <= s.len();
        invariant acc == Str2Int(s@.subrange(0, i as int));
        let bit: nat = if s[i] == '1' { 1 } else { 0 };
        acc = 2 * acc + bit;
        i += 1;
    }
    acc
}

exec fn nat_to_vec(orig: nat) -> (v: Vec<char>)
  ensures ValidBitString(v@)
  ensures Str2Int(v@) == orig
{
    // Represent orig in binary as sequence MSB .. LSB (last element is LSB).
    let mut n: nat = orig;
    let mut v: Vec<char> = Vec::new();
    if n == 0 {
        // Leave v empty; Str2Int(empty) == 0
        return v;
    }

    // Find highest exponent e such that Pow2(e) <= n < Pow2(e+1)
    let mut pow: nat = 1;
    let mut e: usize = 0;
    while pow * 2 <= n {
        invariant pow >= 1;
        invariant pow == Pow2(e as nat);
        pow = pow * 2;
        e += 1;
    }
    // Now pow == Pow2(e) and Pow2(e) <= n < Pow2(e+1)

    let total_len: usize = e + 1;
    let mut rem: usize = total_len;
    // Maintain invariant: orig == Str2Int(v@) * Pow2(rem as nat) + n
    while rem > 0 {
        invariant rem <= total_len;
        invariant orig == Str2Int(v@) * Pow2(rem as nat) + n;
        // current highest power for remaining bits is Pow2(rem-1) == pow
        invariant pow == Pow2((rem - 1) as nat);
        if n >= pow {
            v.push('1');
            n = n - pow;
        } else {
            v.push('0');
        }
        rem -= 1;
        // safe to divide by 2 because pow is a power of two
        pow = pow / 2;
    }

    // After loop, rem == 0, pow == Pow2(0) == 1, and n == 0
    proof {
        // From the loop invariant with rem == 0:
        // orig == Str2Int(v@) * Pow2(0) + n  ==> orig == Str2Int(v@) + n
    }
    // Ensure remainder is zero
    assert(n == 0);
    // v contains only '0'/'1' characters
    // Str2Int(v@) == orig follows from invariant with rem == 0
    v
}
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let n1 = seq_to_nat(s1);
    let n2 = seq_to_nat(s2);
    let res = nat_to_vec(n1 - n2);
    res
}
// </vc-code>

fn main() {}
}