

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method ContainsSequence(list: seq<seq<int>>, sub: seq<int>) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |list| && sub == list[i])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := false;
  while i < |list|
    invariant 0 <= i <= |list|
    invariant result <==> (exists j :: 0 <= j < i && sub == list[j])
    decreases |list| - i
  {
    if list[i] == sub {
      result := true;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>

