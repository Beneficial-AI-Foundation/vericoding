// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method reverse(a: array<int>) returns (result: seq<int>)
    ensures
        |result| == a.Length &&
        forall i :: 0 <= i < |result| ==> result[i] == a[a.Length - 1 - i]
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == a[a.Length - 1 - j]
  {
    result := result + [a[a.Length - 1 - i]];
    i := i + 1;
  }
}
// </vc-code>
