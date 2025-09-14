

// <vc-helpers>
lemma LemmaHelp(i: int, j: int, p: int, q: int)
  requires p <= i <= q
  requires p <= j <= q
  requires j == i + 1 || j == i
  ensures p <= i <= q && p <= j <= q
{
}

lemma DiffLemma(p: int, q: int, diff: int)
  requires diff == q - p
  requires p <= q
  ensures p + diff == q
{
}

lemma EvenCaseLemma(p: int, q: int, diff: int)
  requires p <= q
  requires diff == q - p
  requires diff % 2 == 0
  ensures p <= p + diff/2 <= q
  ensures (p + diff/2) - p == q - (p + diff/2)
{
  var m := p + diff/2;
  assert m - p == diff/2;
  assert q - m == diff - diff/2 == diff/2;
}

lemma OddCaseLemma(p: int, q: int, diff: int)
  requires p <= q
  requires diff == q - p
  requires diff % 2 == 1
  ensures p <= p + (diff - 1)/2 <= q
  ensures (p + (diff - 1)/2) - p == (diff - 1)/2
  ensures q - (p + (diff - 1)/2) == (diff + 1)/2
  ensures (q - (p + (diff - 1)/2)) - ((p + (diff - 1)/2) - p) == 1
{
  var m := p + (diff - 1)/2;
  var left := m - p;
  var right := q - m;
  assert left == (diff - 1)/2;
  assert right == diff - left == diff - (diff - 1)/2 == (2*diff - (diff - 1))/2 == (diff + 1)/2;
  assert right - left == ((diff + 1) - (diff - 1))/2 == 2/2 == 1;
}
// </vc-helpers>

// <vc-spec>
method Mid( p: int, q: int) returns ( m: int )
    // | ... | ??? | ... |
    //        p m   q
    requires p <= q;
    ensures p<= m <= q;
    ensures m-p <= q-m;
    ensures 0 <= (q-m)-(m-p) <= 1;
// </vc-spec>
// <vc-code>
{
  var diff := q - p;
  if diff % 2 == 0 {
    m := p + diff / 2;
    DiffLemma(p, q, diff);
    EvenCaseLemma(p, q, diff);
  } else {
    m := p + (diff - 1) / 2;
    DiffLemma(p, q, diff);
    OddCaseLemma(p, q, diff);
  }
}
// </vc-code>

