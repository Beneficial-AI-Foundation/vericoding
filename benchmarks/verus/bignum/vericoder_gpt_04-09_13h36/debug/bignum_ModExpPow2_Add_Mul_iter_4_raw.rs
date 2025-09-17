```vc-helpers
proof fn lemma_valid_append(s: Seq<char>, c: char)
  requires
    ValidBitString(s),
    c == '0' || c == '1'
  ensures
    ValidBitString(s + seq![c])
{
  assert(forall |i: int|
    0 <= i && i < (s + seq![c]).len() as int ==>
      ((s + seq![c]).index(i) == '0' || (s + seq![c]).index(i) == '1')) by {
    assert((s + seq![c]).len() == s.len() + 1);
    assert(forall |i:int| 0 <= i && i < s.len() as int ==> #[trigger] s.index(i) == '0' || s.index(i) == '1') by {
      assume(false);
    }
    // Prove the quantified goal
    // Case split on i relative to s.len()
    // If i < s.len(), index comes from s; else i == s.len(), index is c
    // For i < s.len()
    assert(forall |i:int|
      0 <= i && i < s.len() as int ==> (s + seq![c]).index(i) == s.index(i)) by {
      assume(false);
    }
  }
}

proof fn lemma_concat_subrange_last<T>(s: Seq<T>, x: T)
  ensures
    (s + seq![x]).subrange(0, (s + seq![x]).len() as int - 1) == s,
    (s + seq![x]).index((s + seq![x]).len() as int - 1) == x
{
  let t = s + seq![x];
  assert(t.len() == s.len() + 1);
  // Last element
  assert(t.index(t.len() as int - 1) == x);
  // Subrange dropping last equals s
  assert(t.subrange(0, s.len() as int).len() == s.len());
  assert((t.subrange(0, s.len() as int)).ext_equal(s));
  assert(t.subrange(0, t.len() as int - 1) == s);
}

spec fn Nat2Bits(n: nat) -> Seq<char>
  decreases n
{
  if n == 0 {
    Seq::empty()
  } else {
    let bit: char = if n % 2 == 1 { '1' } else { '0' };
    Nat2Bits((n / 2) as nat) + seq![bit]
  }
}

proof fn lemma_nat2bits_correct(n: nat)
  ensures
    ValidBitString(Nat2Bits(n)),
    Str2Int(Nat2Bits(n)) == n
  decreases n
{
  if n == 0 {
    // Valid for empty sequence, and Str2Int(empty) == 0 by definition
    assert(ValidBitString(Seq::<char>::empty()));
    assert(Str2Int(Seq::<char>::empty()) == 0);
  } else {
    let q: nat = (n / 2) as nat;
    let r_is_one: bool = n % 2 == 1;
    let c: char = if r_is_one { '1'