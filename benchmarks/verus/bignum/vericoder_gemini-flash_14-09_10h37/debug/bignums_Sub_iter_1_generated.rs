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
spec fn to_bit_seq(n: nat) -> Seq<char>
  decreases n
{
  if n == 0 {
    seq!['0']
  } else if n == 1 {
    seq!['1']
  } else {
    let remainder = n % 2;
    let quotient = n / 2;
    to_bit_seq(quotient).snoc(if remainder == 1 { '1' } else { '0' })
  }
}

lemma fn lemma_Str2Int_to_bit_seq(n: nat)
    ensures Str2Int(to_bit_seq(n)) == n
    decreases n
{
    if n > 1 {
        let remainder = n % 2;
        let quotient = n / 2;
        lemma_Str2Int_to_bit_seq(quotient);
    }
}

pure fn reverse_seq<T>(s: Seq<T>) -> Seq<T>
    ensures reverse_seq(s).len() == s.len()
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        reverse_seq(s.skip(1)).snoc(s.first())
    }
}

lemma fn lemma_Str2Int_reverse_seq(s: Seq<char>) 
    requires ValidBitString(s)
    ensures Str2Int(reverse_seq(s)) == StrReverseInt(s)
    decreases s.len()
{
    if s.len() > 0 {
        lemma_Str2Int_reverse_seq(s.skip(1));
    }
}

spec fn StrReverseInt(s: Seq<char>) -> nat
    recommends ValidBitString(s)
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let last_char = s.last();
        let current_val = if last_char == '1' { (1 nat) * (2 nat).pow((s.len() - 1) as nat) } else { 0 nat };
        StrReverseInt(s.subrange(0, s.len() as int - 1)) + current_val
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
  let n1 = Str2Int(s1@);
  let n2 = Str2Int(s2@);
  let diff = n1 - n2;
  lemma_Str2Int_to_bit_seq(diff);
  let r = to_bit_seq(diff);
  r.to_vec()
}
// </vc-code>

fn main() {}
}


