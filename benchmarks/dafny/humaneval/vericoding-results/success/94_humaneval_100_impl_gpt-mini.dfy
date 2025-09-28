// <vc-preamble>

predicate ValidInput(n: int)
{
    n > 0
}

predicate ValidPile(pile: seq<int>, n: int)
{
    && |pile| == n
    && (n > 0 ==> |pile| > 0 && pile[0] == n)
    && (forall i :: 0 <= i < |pile| ==> pile[i] == n + 2 * i)
    && (forall i :: 0 <= i < |pile| - 1 ==> pile[i+1] == pile[i] + 2)
}
// </vc-preamble>

// <vc-helpers>
lemma DummyHelper() ensures true { }
// </vc-helpers>

// <vc-spec>
method make_a_pile(n: int) returns (pile: seq<int>)
    requires ValidInput(n)
    ensures ValidPile(pile, n)
// </vc-spec>
// <vc-code>
{
  var s: seq<int> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |s| == i
    invariant forall j :: 0 <= j < i ==> s[j] == n + 2 * j
    decreases n - i
  {
    s := s + [n + 2 * i];
    i := i + 1;
  }
  pile := s;
}
// </vc-code>
