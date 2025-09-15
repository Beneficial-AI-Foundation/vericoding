// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method reverse(s: seq<int>) returns (rev: seq<int>)

  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed type errors by using a mutable array and converting to sequence at the end */
  var n := |s|;
  var arr := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> arr[j] == s[n - 1 - j]
  {
    arr[i] := s[n - 1 - i];
    i := i + 1;
  }
  rev := arr[..];
}
// </vc-code>
