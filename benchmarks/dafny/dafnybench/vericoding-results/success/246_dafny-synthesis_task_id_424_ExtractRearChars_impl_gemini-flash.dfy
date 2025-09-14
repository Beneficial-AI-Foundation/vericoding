

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ExtractRearChars(l: seq<string>) returns (r: seq<char>)
    requires forall i :: 0 <= i < |l| ==> |l[i]| > 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[i][|l[i]| - 1]
// </vc-spec>
// <vc-code>
{
  var result: seq<char> := [];
  var i: int := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == l[k][|l[k]| - 1]
  {
    result := result + [l[i][|l[i]| - 1]];
    i := i + 1;
  }
  return result;
}
// </vc-code>

