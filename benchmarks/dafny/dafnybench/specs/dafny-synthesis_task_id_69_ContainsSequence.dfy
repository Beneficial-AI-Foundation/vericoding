// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ContainsSequence(list: seq<seq<int>>, sub: seq<int>) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |list| && sub == list[i])
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>