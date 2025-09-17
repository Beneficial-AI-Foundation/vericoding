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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@),
   t@.len() > 0,
   t@.len() > 1 ==> t@[0] != '0',
   ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    // Check all characters are '0' or '1'
    let mut all_valid = true;
    let mut k: usize = 0;
    while k < s.len() {
        let c = s[k];
        if c != '0' && c != '1' {
            all_valid = false;
            break;
        }
        k += 1;
    }
    if !all_valid {
        let mut r = Vec::new();
        r.push('0');
        return r;
    }
    // Find first '1'
    let mut first_one: int = -1;
    let mut i: int = 0;
    while i < s.len() as int {
        if s[i as usize] == '1' {
            first_one = i;
            break;
        }
        i += 1;
    }
    if first_one == -1 {
        let mut r = Vec::new();
        r.push('0');
        return r;
    }
    let mut res = Vec::new();
    let mut j: usize = first_one as usize;
    while j < s.len() {
        res.push(s[j]);
        j += 1;
    }
    res
}
// </vc-code>

// <vc-helpers>
exec fn parse_bits(s: &[char]) -> (n: nat)
    requires
        ValidBitString(s@),
    ensures
        n == Str2Int(s@),
{
    let mut acc: nat = 0;
    let mut i: int = 0;
    while i < s.len() as int
        invariant
            acc == Str2Int(s@.subrange(0, i)),
        decreases s.len() as int - i
    {
        let c = s[i as usize];
        let bit = if c == '1' { 1 } else { 0 };
        acc = acc * 2 + bit;
        i += 1;
    }
    acc
}

exec fn nat_to_vec(n: nat) -> (v: Vec<char>)
    ensures
        ValidBitString(v@),
        Str2Int(v@) == n,
    decreases
        n
{
    if n == 0 {
        let mut r = Vec::new();
        r.push('0');
        r
    } else {
        let mut v = nat_to_vec(n / 2);
        let b = if n % 2 == 1 { '1' } else { '0' };
        if v.len() == 1 && v[0] == '0' {
            let mut r = Vec::new();
            r.push(b);
            r
        } else {
            v.push(b);
            v
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures ValidBitString(res@), 
    Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let n1 = parse_bits(s1);
    let n2 = parse_bits(s2);
    let sum = n1 + n2;
    let res = nat_to_vec(sum);
    res
}
// </vc-code>

fn main() {}
}


