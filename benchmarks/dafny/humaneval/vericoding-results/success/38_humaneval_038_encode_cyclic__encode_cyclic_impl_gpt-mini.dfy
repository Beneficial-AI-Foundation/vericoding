// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): IsIdx helper for index bounds */
function IsIdx(n: int, i: int): bool { 0 <= i < n }
// </vc-helpers>

// <vc-spec>
method encode_cyclic(s: seq<int>) returns (res: seq<int>) 

    ensures |s| == |res|
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i + 1])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 2 ==> res[i] == s[i - 2])
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): process full triples then copy remainder */
  var n := |s|;
  var arr := new int[n];
  var m := n - n % 3;
  var k := 0;
  while k * 3 < m
    invariant 0 <= k <= m/3
    invariant forall j :: 0 <= j < 3*k ==> (if j % 3 == 0 then arr[j] == s[j + 1] else if j % 3 == 1 then arr[j] == s[j + 1] else arr[j] == s[j - 2])
  {
    var t := 3 * k;
    arr[t] := s[t + 1];
    arr[t + 1] := s[t + 2];
    arr[t + 2] := s[t];
    k := k + 1;
  }
  var i := m;
  while i < n
    invariant m <= i <= n
    invariant forall j :: 0 <= j < m ==> (if j % 3 == 0 then arr[j] == s[j + 1] else if j % 3 == 1 then arr[j] == s[j + 1] else arr[j] == s[j - 2])
    invariant forall j :: m <= j < i ==> arr[j] == s[j]
  {
    arr[i] := s[i];
    i := i + 1;
  }
  res := arr[..];
}
// </vc-code>
