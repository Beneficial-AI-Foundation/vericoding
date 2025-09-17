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
  ensures Str2Int(Int2StrSeq(n)) == n && ValidBitString(Int2StrSeq(n))
  decreases n
{
  if n == 0 {
    // Int2StrSeq(0) == empty, Str2Int(empty) == 0 holds by definition
    assert(Int2StrSeq(0).len() == 0);
    assert(Str2Int(Int2StrSeq(0)) == 0);
    // empty sequence is trivially a valid bit string
    assert(forall |i: int| 0 <= i && i < Int2StrSeq(0).len() as int ==> (Int2StrSeq(0).index(i) == '0' || Int2StrSeq(0).index(i) == '1'));
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

    // Apply inductive hypothesis: Str2Int(q) == (n/2)
    assert(Str2Int(q) == (n / 2));

    // arithmetic: 2*(n/2) + (n%2) == n
    assert(2 * (n / 2) + (if n % 2 == 1 { 1 } else { 0 }) == n);

    // combine
    assert(Str2Int(s) == n);

    // Now prove ValidBitString(s)
    // From inductive hypothesis, q is a valid bit string
    assert(forall |i: int| 0 <= i && i < q.len() as int ==> (q.index(i) == '0' || q.index(i) == '1'));
    // Show every index of s is '0' or '1'
    assert(forall |i: int| 0 <= i && i < s.len() as int ==>
      ({
        if i < q.len() as int {
          // s.index(i) == q.index(i)
          s.index(i) == q.index(i)
        } else {
          // i == q.len(), last element equals b
          s.index(i) == b
        }
      } ==>
      ({
        if i < q.len() as int {
          q.index(i) == '0' || q.index(i) == '1'
        } else {
          b == '0' || b == '1'
        }
      }))
    );
    // Now simplify to obtain validity
    assert(forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1'));
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
  // proof of correctness of Int2StrSeq (both Str2Int equality and validity)
  proof {
    Int2StrSeq_valid_and_correct(sum);
  }

  // Convert the sequence into a Vec<char> by pushing elements in order
  let mut res = Vec::<char>::new();
  let mut i: nat = 0;
  let len: nat = seq_sum.len();
  while (i < len)
    invariant i <= len && res.len() == i && res@ == seq_sum.subrange(0, i as int)
    decreases (len - i)
  {
    // capture old values for reasoning
    let old_i: nat = i;
    let old_res_spec: Seq<char> = res@;

    let c: char = seq_sum.index(old_i as int);
    // push the character corresponding to seq_sum[old_i]
    res.push(c);

    // update index
    i = old_i + 1;

    // now prove the invariants hold after the step
    // old_res_spec == seq_sum.subrange(0, old_i) by the loop invariant
    assert(old_res_spec == seq_sum.subrange(0, old_i as int));
    // res@ equals old_res_spec + seq![c] after push
    assert(res@ == old_res_spec + seq![c]);
    // seq_sum.subrange(0, old_i + 1) equals seq_sum.subrange(0, old_i) + seq![seq_sum.index(old_i)]
    assert(seq_sum.subrange(0, (old_i + 1) as int) == seq_sum.subrange(0, old_i as int) + seq![seq_sum.index(old_i as int)]);
    // combine to get res@ == seq_sum.subrange(0, i)
    assert(res@ == seq_sum.subrange(0, i as int));
    // length invariant
    assert(res.len() == i);
  }

  // At this point res@ == seq_sum, so it satisfies the spec
  proof {
    // From the proof lemma we have Str2Int(seq_sum) == sum and seq_sum is a valid bit string.
    // These, together with res@ == seq_sum, conclude the ensures clause.
    assert(res@ == seq_sum);
    assert(Str2Int(seq_sum) == sum);
    assert(ValidBitString(seq_sum));
    // therefore
    assert(Str2Int(res@) == sum);
    assert(ValidBitString(res@));
  }
  return res;
}
// </vc-code>

fn main() {}
}