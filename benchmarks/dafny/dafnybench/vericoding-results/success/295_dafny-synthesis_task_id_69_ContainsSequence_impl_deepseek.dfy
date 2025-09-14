

// <vc-helpers>
lemma SequenceEqualImpliesExistsIndex(list: seq<seq<int>>, sub: seq<int>, i: int)
  requires 0 <= i < |list|
  requires sub == list[i]
  ensures exists i :: 0 <= i < |list| && sub == list[i]
{
}

lemma ExistsIndexImpliesSequenceEqual(list: seq<seq<int>>, sub: seq<int>)
  requires exists i :: 0 <= i < |list| && sub == list[i]
  ensures (exists i :: 0 <= i < |list| && sub == list[i])
{
}
// </vc-helpers>

// <vc-spec>
method ContainsSequence(list: seq<seq<int>>, sub: seq<int>) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |list| && sub == list[i])
// </vc-spec>
// <vc-code>
{
  var index := 0;
  while index < |list|
    invariant index <= |list|
    invariant forall j :: 0 <= j < index ==> list[j] != sub
    invariant !(exists i :: 0 <= i < index && sub == list[i])
  {
    if list[index] == sub {
      return true;
    }
    index := index + 1;
  }
  return false;
}
// </vc-code>

