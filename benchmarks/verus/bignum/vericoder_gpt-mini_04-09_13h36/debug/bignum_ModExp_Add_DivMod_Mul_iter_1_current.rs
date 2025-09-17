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
spec fn Int2StrSeq(n: nat) -> Seq<char>
  decreases n
{
  if n == 0 {
    Seq::empty()
  } else {
    let q = Int2StrSeq(n / 2);
    q + seq![ if n % 2 == 1 { '1' } else { '0' } ]
  }
}

proof fn Int2StrSeq_valid_and_correct(n: nat)
  decreases n
{
  if n == 0 {
    // Int2StrSeq(0) == empty, Str2Int(empty) == 0 holds by definition
    assert(Int2StrSeq(0).len() == 0);
    assert(Str2Int(Int2StrSeq(0)) == 0);
  } else {
    // inductive hypothesis
    Int2StrSeq_valid_and_correct(n / 2);

    let q = Int2StrSeq(n / 2);
    let b = if n % 2 == 1 { '1' } else { '0' };
    let s = q + seq![b];

    // s is q with b appended
    assert(s.len() as int == q.len() as int + 1);
    assert(s.subrange(0, s.len() as int - 1) == q);
    assert(s.index(s.len() as int - 1) == b);

    // By definition of Str2Int on non-empty sequence:
    // Str2Int(s) == 2 * Str2Int(s.subrange(0, len-1)) + bit
    assert(Str2Int(s) == 2 * Str2Int(q) + (if b == '1' { 1 } else { 0 }));

    // Apply inductive hypothesis
    assert(Str2Int(q) == (n / 2));

    // arithmetic: 2*(n/2) + (n%2) == n
    assert(2 * (n / 2) + (if n % 2 == 1 { 1 } else { 0 }) == n);

    // combine
    assert(Str2Int(s) == n);
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
  // Compute integer values of inputs
  let n1: nat = Str2Int(s1@);
  let n2: nat = Str2Int(s2@);
  let sum: nat = n1 + n2;

  // Build the sequence representation of the sum
  let seq_sum: Seq<char> = Int2StrSeq(sum);
  // proof of correctness of Int2StrSeq
  proof {
    Int2StrSeq_valid_and_correct(sum);
  }

  // Convert the sequence into a Vec<char> by pushing elements in order
  let mut res = Vec::<char>::new();
  let mut i: int = 0;
  while i < seq_sum.len() as int
    invariant 0 <= i && i <= seq_sum.len() as int
    invariant res.len() as int == i
    invariant res@ == seq_sum.subrange(0, i)
  {
    res.push(seq_sum.index(i));
    i = i + 1;
  }

  // At this point res@ == seq_sum, so it satisfies the spec
  assert(res@ == seq_sum);
  return res;
}
// </vc-code>

fn main() {}
}