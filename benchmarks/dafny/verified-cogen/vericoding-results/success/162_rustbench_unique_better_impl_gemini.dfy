// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method UniqueBetter(a: array<int>) returns (result: seq<int>)
    requires
        forall i: int, j: int ::
            0 <= i && i < j && j < a.Length ==> a[i] <= a[j]
    ensures
        forall i: int, j: int ::
            0 <= i && i < j && j < |result| ==> result[i] < result[j]
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k, l :: 0 <= k < l < |result| ==> result[k] < result[l]
    invariant forall x :: x in result ==> (exists j :: 0 <= j < i && a[j] == x)
  {
    if |result| == 0 || a[i] > result[|result| - 1]
    {
      result := result + [a[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
