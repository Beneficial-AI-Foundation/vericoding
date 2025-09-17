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
        assert(Exp_int(2, 0) == 1);
        assert(Exp_int(2, 1) == 2 * Exp_int(2, 0));
    } else {
        exp_mul2((n - 1) as nat);
        // By definition Exp_int(2, n+1) == 2 * Exp_int(2, n)
        assert(Exp_int(2, n + 1) == 2 * Exp_int(2, n));
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
    let n1 = s1.len();
    let n2 = s2.len();
    let mut k: usize = 0;
    let mut carry: u8 = 0;
    let mut tmp: Vec<char> = Vec::new();

    // add from least significant bit to most significant
    let max_len = if n1 > n2 { n1 } else { n2 };
    while k < max_len
        invariant k <= max_len
        invariant ValidBitString(tmp@)
        decreases max_len - k
    {
        let b1 = if k < n1 { s1[n1 - 1 - k] } else { '0' };
        let b2 = if k < n2 { s2[n2 - 1 - k] } else { '0' };
        let v1: u8 = if b1 == '1' { 1 } else { 0 };
        let v2: u8 = if b2 == '1' { 1 } else { 0 };
        let sum = carry + v1 + v2;
        let bit = if sum % 2 == 1 { '1' } else { '0' };
        assert(bit == '0' || bit == '1');
        tmp.push(bit);
        carry = if sum >= 2 { 1 } else { 0 };
        k += 1;
    }

    if carry == 1 {
        tmp.push('1');
    }

    // reverse tmp to get most-significant-first order
    let mut res: Vec<char> = Vec::new();
    let mut idx: usize = tmp.len();
    while idx > 0
        invariant idx <= tmp.len()
        invariant ValidBitString(res@)
        decreases idx
    {
        idx -= 1;
        assert(tmp[idx] == '0' || tmp[idx] == '1');
        res.push(tmp[idx]);
    }

    // Return the result vector
    res
}
// </vc-code>

fn main() {}
}