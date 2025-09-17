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
spec fn Int2Bits(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::<char>::empty().push('0')
    } else {
        Int2Bits(n / 2).push(if n % 2 == 0 { '0' } else { '1' })
    }
}

proof fn lemma_seq_subrange_push(s: Seq<char>, i: int)
    requires
        0 <= i,
        i < s.len() as int,
    ensures
        s.subrange(0, i).push(s.index(i)) == s.subrange(0, i + 1),
{
}

proof fn lemma_subrange_full(s: Seq<char>)
    ensures
        s.subrange(0, s.len() as int) == s,
{
}

proof fn lemma_Valid_push(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        ValidBitString(s.push(c)),
{
}

proof fn lemma_Str2Int_push(s: Seq<char>, c: char)
    ensures
        Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat }),
{
}

proof fn lemma_Int2Bits_valid(n: nat)
    decreases n
    ensures
        ValidBitString(Int2Bits(n)),
{
    if n == 0 {
    } else {
        lemma_Int2Bits_valid(n / 2);
        lemma_Valid_push(Int2Bits(n / 2), if n % 2 == 0 { '0' } else { '1' });
    }
}

proof fn lemma_Int2Bits_value(n: nat)
    decreases n
    ensures
        Str2Int(Int2Bits(n)) == n,
{
    if n == 0 {
    } else {
        lemma_Int2Bits_value(n / 2);
        lemma_Str2Int_push(Int2Bits(n / 2), if n % 2 == 0 { '0' } else { '1' });
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let n1 = Str2Int(s1@);
    let n2 = Str2Int(s2@);
    let n = n1 * n2;

    let mut res: Vec<char> = Vec::new();
    let mut i: int = 0;
    while i < Int2Bits(n).len() as int
        invariant
            0 <= i,
            i <= Int2Bits(n).len() as int,
            res@ == Int2Bits(n).subrange(0, i),
        decreases Int2Bits(n).len() as int - i
    {
        let c = Int2Bits(n).index(i);
        res.push(c);
        proof {
            lemma_seq_subrange_push(Int2Bits(n), i);
        }
        i = i + 1;
    }
    proof {
        lemma_subrange_full(Int2Bits(n));
        lemma_Int2Bits_valid(n);
        lemma_Int2Bits_value(n);
    }
    res
}
// </vc-code>

fn main() {}
}
