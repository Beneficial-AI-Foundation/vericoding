

// <vc-helpers>
function ArrayToSeq(a: array<int>, j: int, n: int): seq<int>
  requires 0 <= j <= n <= a.Length
  reads a
  ensures |ArrayToSeq(a, j, n)| == n - j
  ensures forall i | 0 <= i < n - j :: ArrayToSeq(a, j, n)[i] == a[j + i]
  decreases n - j
{
  if j == n then []
  else [a[j]] + ArrayToSeq(a, j+1, n)
}
// </vc-helpers>

// <vc-spec>
method AppendArrayToSeq(s: seq<int>, a: array<int>) returns (r: seq<int>)
    requires a != null
    ensures |r| == |s| + a.Length
    ensures forall i :: 0 <= i < |s| ==> r[i] == s[i]
    ensures forall i :: 0 <= i < a.Length ==> r[|s| + i] == a[i]
// </vc-spec>
// <vc-code>
{
  r := s;
  var i := 0;
  while i < a.Length 
    invariant 0 <= i <= a.Length
    invariant |r| == |s| + i
    invariant forall k :: 0 <= k < |s| ==> r[k] == s[k]
    invariant forall k :: 0 <= k < i ==> r[|s| + k] == a[k]
  {
    r := r + [a[i]];
    i := i + 1;
  }
}
// </vc-code>

