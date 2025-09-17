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
proof fn lemma_valid_Int2Str(n: nat)
  ensures ValidBitString(Int2Str(n))
  decreases n
{
  if n == 0 {
    assert(ValidBitString(Seq::<char>::empty()));
  } else {
    let s = Int2Str(n / 2);
    let c = if n % 2 == 1 { '1' } else { '0' };
    lemma_valid_Int2Str(n / 2);
    assert(s.push(c).len() == s.len() + 1);
    assert forall |i: int|
      0 <= i && i < s.push(c).len() as int
      implies #[trigger] s.push(c).index(i) == '0' || s.push(c).index(i) == '1'
    by {
      if i < s.len() as int {
        assert(0 <= i && i < s.len() as int);
        assert(s.push(c).index(i) == s.index(i));
        assert(ValidBitString(s));
        assert(s.index(i) == '0' || s.index(i) == '1');
      } else {
        assert(i == s.len() as int);
        assert(s.push(c).index(i) == c);
        assert(c == '0' || c == '1');
      }
    }
  }
}

proof fn lemma_Str2Int_Int2Str(n: nat)
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 {
    assert(Str2Int(Seq::<char>::empty()) == 0);
  } else {
    let s = Int2Str(n / 2);
    let c = if n % 2 == 1 { '1' } else { '0' };

    // IH and validity for substructure
    lemma_Str2Int_Int2Str(n / 2);
    lemma_valid_Int2Str(n / 2);
    assert(ValidBitString(s));

    let t = s.push(c);
    assert(t.len() > 0);
    assert(t.subrange(0, t.len() as int - 1) == s);
    assert(t.index(t.len() as int - 1) == c);

    // By the definition of Str2Int on non-empty sequences
    assert(Str2Int(t) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat }));

    // Use IH: Str2Int(s) == n/2 and c corresponds to n%2
    assert(2 * (n / 2) + (if c == '1' { 1nat } else { 0nat }) == 2 * (n / 2) + (n % 2)) by {
      if n % 2 == 1 {
        assert(c == '1');
      } else {
        assert(c == '0');
      }
    };
    assert(n == 2 * (n / 2) + (n % 2));

    assert(Str2Int(t) == n);
  }
}

spec fn Int2Str(n: nat) -> Seq<char>
  decreases n
{
  if n == 0 {
    Seq::<char>::empty()
  } else {
    Int2Str(n / 2).push(if n % 2 == 1 { '1' } else { '0' })
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
  proof {
    lemma_valid_Int2Str(Str2Int(s1@) * Str2Int(s2@));
    lemma_Str2Int_Int2Str(Str2Int(s1@) * Str2Int(s2@));
  }
  let res = Vec::<char>::from_seq(Int2Str(Str2Int(s1@) * Str2Int(s2@)));
  res
}
// </vc-code>

fn main() {}
}