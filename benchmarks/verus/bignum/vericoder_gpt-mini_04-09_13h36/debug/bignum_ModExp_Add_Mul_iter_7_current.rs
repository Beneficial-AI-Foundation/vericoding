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
spec fn Nat2Str(n: nat) -> Seq<char>
  recommends n >= 0
  decreases n
{
  if n == 0 {
    Seq::<char>::empty()
  } else {
    let b: char = if n % 2 == 1 { '1' } else { '0' };
    Nat2Str(n / 2) + seq![b]
  }
}

proof fn str2int_snoc(s: Seq<char>, c: char)
  requires ValidBitString(s + seq![c])
  ensures Str2Int(s + seq![c]) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat })
{
  let t = s + seq![c];
  // By definition of Str2Int on non-empty sequence:
  assert(t.len() as int >= 1);
  assert(Str2Int(t) ==
         2 * Str2Int(t.subrange(0, t.len() as int - 1))
         + (if t.index(t.len() as int - 1) == '1' { 1nat } else { 0nat }));
  // t.subrange(0, t.len()-1) == s, and last element == c
  assert(t.subrange(0, t.len() as int - 1) == s);
  assert(t.index(t.len() as int - 1) == c);
  // conclude
  assert(Str2Int(s + seq![c]) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat }));
}

proof fn Nat2Str_valid(n: nat)
  ensures ValidBitString(Nat2Str(n))
  decreases n
{
  if n == 0 {
    // empty sequence is valid
  } else {
    let b: char = if n % 2 == 1 { '1' } else { '0' };
    Nat2Str_valid(n / 2);
    // concat preserves ValidBitString
    assert(ValidBitString(Nat2Str(n / 2)));
    assert(ValidBitString(Nat2Str(n / 2) + seq![b]));
  }
}

proof fn Nat2Str_spec(n: nat)
  ensures Str2Int(Nat2Str(n)) == n
  decreases n
{
  if n == 0 {
    // Str2Int(empty) == 0 by definition
  } else {
    let b: char = if n % 2 == 1 { '1' } else { '0' };
    // induction on n/2
    Nat2Str_spec(n / 2);
    // use snoc lemma
    str2int_snoc(Nat2Str(n / 2), b);
    // combine facts
    assert(Str2Int(Nat2Str(n / 2) + seq![b]) ==
           2 * Str2Int(Nat2Str(n / 2)) + (if b == '1' { 1nat } else { 0nat }));
    assert(Str2Int(Nat2Str(n / 2)) == n / 2);
    // n == 2*(n/2) + n%2
    assert(n == 2 * (n / 2) + n % 2);
    assert((if b == '1' { 1nat } else { 0nat }) == n % 2);
    assert(Str2Int(Nat2Str(n)) == n);
  }
}

// helper: full subrange equals sequence
proof fn seq_subrange_full<T>(s: Seq<T>)
  ensures s.subrange(0, s.len() as int) == s
{
  // by definition of subrange when taking full range
}
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  let sum: nat = Str2Int(s1@) + Str2Int(s2@);
  let seq: Seq<char> = Nat2Str(sum);
  // build result Vec by copying seq
  let mut res = Vec::<char>::new();
  let mut i: int = 0;
  while i < seq.len() as int
    invariant { 0 <= i && i <= seq.len() as int && res.len() as int == i && res@ == seq.subrange(0, i) }
    decreases (seq.len() as nat - i as nat)
  {
    let c = seq.index(i);
    res.push(c);
    i = i + 1;
  }

  proof {
    // seq is a valid bitstring and corresponds to sum
    Nat2Str_valid(sum);
    Nat2Str_spec(sum);
    // after loop, res@ == seq
    assert(i == seq.len() as int);
    assert(res.len() as int == i);
    assert(res@ == seq.subrange(0, i));
    seq_subrange_full(seq);
    assert(seq.subrange(0, seq.len() as int) == seq);
    assert(res@ == seq);
    assert(Str2Int(res@) == sum);
  }

  return res;
}
// </vc-code>

fn main() {}
}