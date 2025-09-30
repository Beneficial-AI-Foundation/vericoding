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

// </vc-helpers>

// <vc-spec>
method make_a_pile(n: int) returns (pile: seq<int>)
    requires ValidInput(n)
    ensures ValidPile(pile, n)
// </vc-spec>
// <vc-code>
{
  pile := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |pile| == i
    invariant forall j :: 0 <= j < i ==> pile[j] == n + 2 * j
    invariant i > 0 ==> pile[0] == n
    invariant forall j :: 0 <= j < i - 1 ==> pile[j+1] == pile[j] + 2
  {
    pile := pile + [n + 2 * i];
    i := i + 1;
  }
}
// </vc-code>
