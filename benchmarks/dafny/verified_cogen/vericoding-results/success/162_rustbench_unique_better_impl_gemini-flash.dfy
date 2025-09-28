// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Contains(s: seq<int>, x: int): bool { exists i :: 0 <= i < |s| && s[i] == x }
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
  if a.Length == 0 {
    return;
  }

  var currentUnique := a[0];
  result := [currentUnique];

  var i := 1;
  while i < a.Length
    invariant 0 < i <= a.Length
    invariant forall k: int, l: int :: 0 <= k && k < l && l < |result| ==> result[k] < result[l]
    invariant forall k :: 0 <= k < |result| ==> Contains(a[..i], result[k])
    invariant (i > 0 && |result| > 0) ==> result[|result|-1] == currentUnique
    invariant |result| <= i
  {
    if a[i] > currentUnique {
      currentUnique := a[i];
      result := result + [currentUnique];
    }
    i := i + 1;
  }
}
// </vc-code>
