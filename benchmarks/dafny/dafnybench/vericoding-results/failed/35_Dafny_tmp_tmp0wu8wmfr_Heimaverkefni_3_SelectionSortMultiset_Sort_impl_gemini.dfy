// <vc-preamble>
method MinOfMultiset( m: multiset<int> ) returns( min: int )
    ensures min in m;
    ensures forall z | z in m :: min <= z;
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>
method PopMin(m: multiset<int>) returns (min: int, rest: multiset<int>)
  requires m != multiset{}
  ensures min in m
  ensures rest == m - multiset{min}
  ensures forall z :: z in rest ==> min <= z
{
  var x :| x in m;
  min := x;
  var processed := multiset{x};
  var unprocessed := m - multiset{x};
  while unprocessed != multiset{}
    invariant processed + unprocessed == m
    invariant min in processed
    invariant forall y :: y in processed ==> min <= y
  {
    var y :| y in unprocessed;
    if y < min {
      min := y;
    }
    processed := processed + multiset{y};
    unprocessed := unprocessed - multiset{y};
  }
  assert processed == m;
  rest := m - multiset{min};
}
// </vc-helpers>

// <vc-spec>
method Sort( m: multiset<int> ) returns ( s: seq<int> )

    ensures multiset(s) == m;
    ensures forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
// </vc-spec>
// <vc-code>
{
  s := [];
  var current_m := m;
  while current_m != multiset{}
    invariant multiset(s) + current_m == m
    invariant forall p, q | 0 <= p < q < |s| :: s[p] <= s[q]
    invariant |s| > 0 ==> forall y | y in current_m :: s[|s|-1] <= y
  {
    var min_val, next_m := PopMin(current_m);
    s := s + [min_val];
    current_m := next_m;
  }
}
// </vc-code>
