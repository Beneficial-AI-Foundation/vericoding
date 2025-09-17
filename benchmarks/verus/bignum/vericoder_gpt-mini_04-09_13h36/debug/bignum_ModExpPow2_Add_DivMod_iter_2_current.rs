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
proof fn exp_mult(n: nat)
  ensures Exp_int(2, n + 1) == 2 * Exp_int(2, n)
  decreases n
{
    if n == 0 {
        // Exp_int(2,1) == 2 * Exp_int(2,0)
    } else {
        exp_mult(n - 1);
    }
}

proof fn str2int_concat(p: Seq<char>, s: Seq<char>)
  ensures Str2Int(p + s) == Exp_int(2, s.len()) * Str2Int(p) + Str2Int(s)
  decreases s.len()
{
    if s.len() == 0 {
        // Str2Int(p + []) == 1 * Str2Int(p) + 0
    } else {
        let last_i: int = s.len() as int - 1;
        let last = s.index(last_i);
        let s_init = s.subrange(0, last_i);
        str2int_concat(p, s_init);
        // Inductive step follows from definition of Str2Int
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
    // Compute Str2Int(s1@) as n1
    let mut i: int = 0;
    let len1: int = s1.len() as int;
    let mut n1: nat = 0;
    while i < len1
        invariant 0 <= i && i <= len1
        invariant n1 == Str2Int((s1@).subrange(0, i))
        invariant ValidBitString(s1@)
    {
        let ch = s1[i as usize];
        if ch == '1' {
            n1 = 2 * n1 + 1;
        } else {
            n1 = 2 * n1;
        }
        i += 1;
    }

    // Compute Str2Int(s2@) as n2
    let mut j: int = 0;
    let len2: int = s2.len() as int;
    let mut n2: nat = 0;
    while j < len2
        invariant 0 <= j && j <= len2
        invariant n2 == Str2Int((s2@).subrange(0, j))
        invariant ValidBitString(s2@)
    {
        let ch = s2[j as usize];
        if ch == '1' {
            n2 = 2 * n2 + 1;
        } else {
            n2 = 2 * n2;
        }
        j += 1;
    }

    let mut total: nat = n1 + n2;

    // If total is zero, return empty Vec
    if total == 0 {
        return Vec::<char>::new();
    }

    // Find highest power of two <= total: pow = 2^(len_rem - 1)
    let mut pow: nat = 1;
    let mut len_rem: nat = 1;
    while pow * 2 <= total
        invariant pow >= 1
        invariant len_rem >= 1
        invariant pow == Exp_int(2, len_rem - 1)
        invariant pow <= total
    {
        pow = pow * 2;
        // justify relation after increment
        exp_mult(len_rem - 1);
        len_rem = len_rem + 1;
    }

    // Build result by appending bits from MSB to LSB (push adds new last char)
    let total0 = total;
    let mut rem: nat = total;
    let mut res: Vec<char> = Vec::new();

    while len_rem > 0
        invariant len_rem >= 0
        invariant total0 == Exp_int(2, len_rem) * Str2Int(res@) + rem
        invariant rem < Exp_int(2, len_rem)
        invariant ValidBitString(res@)
    {
        if rem >= pow {
            rem = rem - pow;
            res.push('1');
        } else {
            res.push('0');
        }

        if len_rem >= 1 {
            exp_mult(len_rem - 1);
        }
        len_rem = len_rem - 1;
        pow = pow / 2;
    }

    return res;
}
// </vc-code>

fn main() {}
}