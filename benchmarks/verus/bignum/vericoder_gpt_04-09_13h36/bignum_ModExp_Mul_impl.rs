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
proof fn lemma_valid_push(s: Seq<char>, b: char)
  requires ValidBitString(s), b == '0' || b == '1'
  ensures ValidBitString(s.push(b))
{
  assert forall |i:int| 0 <= i && i < s.push(b).len() as int implies (#[trigger] s.push(b).index(i) == '0' || s.push(b).index(i) == '1') by {
    if i < s.len() as int {
      assert(s.push(b).index(i) == s.index(i));
    } else {
      assert(i == s.len() as int);
      assert(s.push(b).index(i) == b);
    }
  }
}

spec fn Num2Bits(n: nat) -> Seq<char>
  decreases n
{
  if n == 0 {
    Seq::<char>::empty()
  } else {
    let rest = Num2Bits(n / 2);
    let b = if n % 2 == 1 { '1' } else { '0' };
    rest.push(b)
  }
}

proof fn lemma_Str2Int_of_Num2Bits(n: nat)
  ensures Str2Int(Num2Bits(n)) == n
  decreases n
{
  if n == 0 {
  } else {
    let rest = Num2Bits(n / 2);
    let b = if n % 2 == 1 { '1' } else { '0' };
    lemma_Str2Int_of_Num2Bits(n / 2);

    let s = Num2Bits(n);
    assert(s == rest.push(b));

    assert(s.len() > 0);
    assert(s.subrange(0, s.len() as int - 1) == rest) by {
      assert(s.len() == rest.len() + 1);
      assert(s == rest.push(b));
      assert((rest.push(b)).subrange(0, rest.len() as int) == rest);
    }
    assert(s.index(s.len() as int - 1) == b) by {
      assert(s == rest.push(b));
      assert((rest.push(b)).index(rest.len() as int) == b);
      assert(s.len() == rest.len() + 1);
      assert(s.len() as int - 1 == rest.len() as int);
    }

    assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1))
           + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }));

    assert(Str2Int(s.subrange(0, s.len() as int - 1)) == Str2Int(rest));
    assert(s.index(s.len() as int - 1) == b);

    assert((if b == '1' { 1nat } else { 0nat }) == (if n % 2 == 1 { 1nat } else { 0nat }));

    assert(Str2Int(rest) == n / 2);
    assert(2 * (n / 2) + n % 2 == n);
  }
}

proof fn lemma_Valid_Num2Bits(n: nat)
  ensures ValidBitString(Num2Bits(n))
  decreases n
{
  if n == 0 {
  } else {
    lemma_Valid_Num2Bits(n / 2);
    let rest = Num2Bits(n / 2);
    let b = if n % 2 == 1 { '1' } else { '0' };
    assert(b == '0' || b == '1');
    lemma_valid_push(rest, b);
  }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  let prod = Str2Int(s1@) * Str2Int(s2@);
  proof {
    lemma_Str2Int_of_Num2Bits(prod);
    lemma_Valid_Num2Bits(prod);
  }
  let res = Vec::<char>::from_seq(Num2Bits(prod));
  res
}
// </vc-code>

fn main() {}
}