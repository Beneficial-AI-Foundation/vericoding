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
proof fn exp_mul2(n: nat)
  ensures Exp_int(2, n + 1) == 2 * Exp_int(2, n)
{
    if n == 0 {
        // Exp_int(2, 0) == 1, Exp_int(2, 1) == 2
        assert(Exp_int(2, 0) == 1);
        assert(Exp_int(2, 1) == 2);
    } else {
        exp_mul2(n - 1);
        // By definition of Exp_int: Exp_int(2, n+1) = 2 * Exp_int(2, n)
        // The recursive definition of Exp_int gives this directly.
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    // Convert s1 to nat acc1
    let n1 = s1.len();
    let mut i: usize = 0;
    let mut acc1: nat = 0;
    while i < n1
        invariant i <= n1
        invariant acc1 == Str2Int(s1@.subrange(0, i as int))
        decreases (n1 - i)
    {
        let c = s1[i];
        let bit: nat = if c == '1' { 1 } else { 0 };
        acc1 = 2 * acc1 + bit;
        i += 1;
    }

    // Convert s2 to nat acc2
    let n2 = s2.len();
    let mut j: usize = 0;
    let mut acc2: nat = 0;
    while j < n2
        invariant j <= n2
        invariant acc2 == Str2Int(s2@.subrange(0, j as int))
        decreases (n2 - j)
    {
        let c = s2[j];
        let bit: nat = if c == '1' { 1 } else { 0 };
        acc2 = 2 * acc2 + bit;
        j += 1;
    }

    let total: nat = acc1 + acc2;

    // Build resulting bitstring (MSB-first) by extracting bits from total.
    let mut res = Vec::<char>::new();

    if total == 0 {
        // Represent 0 with empty sequence, Str2Int(empty) == 0 holds
        return res;
    }

    let mut rem: nat = total;
    // Invariant: total == rem * Exp_int(2, res.len() as nat) + Str2Int(res@)
    // and res@ is a valid bitstring
    while rem > 0
        invariant rem >= 0
        invariant total == rem * Exp_int(2, res.len() as nat) + Str2Int(res@)
        invariant ValidBitString(res@)
        decreases rem
    {
        let bit: nat = rem % 2;
        rem = rem / 2;
        let ch: char = if bit == 1 { '1' } else { '0' };
        // insert at front to keep MSB-first order
        res.insert(0, ch);

        // After insertion, the invariant holds because:
        // let k = old res.len();
        // old invariant: total == old_rem * 2^k + Str2Int(old_res@)
        // with old_rem = 2*rem + bit
        // then total == rem * 2^(k+1) + (bit * 2^k + Str2Int(old_res@))
        // and Str2Int(new_res@) == bit * 2^k + Str2Int(old_res@)
    }

    return res;
}
// </vc-code>

fn main() {}
}