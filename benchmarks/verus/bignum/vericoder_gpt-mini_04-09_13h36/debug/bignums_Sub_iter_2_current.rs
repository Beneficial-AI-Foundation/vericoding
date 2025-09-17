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

proof fn Str2Int_subrange_last(s: Seq<char>)
    requires ValidBitString(s)
    ensures
        if s.len() == 0 {
            Str2Int(s) == 0
        } else {
            let k = s.len() - 1;
            Str2Int(s) == 2 * Str2Int(s.subrange(0, k as int)) + (if s.index(k as int) == '1' { 1 } else { 0 })
        }
    decreases s.len()
{
    // Follows directly from the definition of Str2Int by case analysis on length
    if s.len() == 0 {
    } else {
    }
}

proof fn Str2Int_prefix_bound(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) < Pow
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
spec fn Pow2(n: nat) -> nat {
    if n == 0 { 1 } else { 2 * Pow2(n - 1) }
}

proof fn Str2Int_subrange_last(s: Seq<char>)
    requires ValidBitString(s)
    ensures
        if s.len() == 0 {
            Str2Int(s) == 0
        } else {
            let k = s.len() - 1;
            Str2Int(s) == 2 * Str2Int(s.subrange(0, k as int)) + (if s.index(k as int) == '1' { 1 } else { 0 })
        }
    decreases s.len()
{
    // Follows directly from the definition of Str2Int by case analysis on length
    if s.len() == 0 {
    } else {
    }
}

proof fn Str2Int_prefix_bound(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) < Pow
// </vc-code>

fn main() {}
}