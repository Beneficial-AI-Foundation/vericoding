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
spec fn Int2Str(n: nat) -> Seq<char>
    ensures
        ValidBitString(result),
        Str2Int(result) == n
    decreases n
{
    if n == 0 {
        Seq::empty()
    } else {
        let temp = n / 2;
        Int2Str(temp as nat).push(if n % 2 == 0 { '0' } else { '1' })
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let val1 = Str2Int(s1@);
    let val2 = Str2Int(s2@);
    let diff: nat = val1 - val2;
    let result_seq = Int2Str(diff);
    let len = result_seq.len();
    let mut res: Vec<char> = Vec::with_capacity(len);
    for i in 0..len
        invariant
            res.len() == i,
            forall |j: int| 0 <= j < i ==> res@[j] == result_seq.index(j)
        decreases len - i
    {
        res.push(result_seq.index(i as int));
    }
    res
}
// </vc-code>

fn main() {}
}


