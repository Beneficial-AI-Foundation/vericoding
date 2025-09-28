// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma LengthAppendSingleton<T>(s: seq<T>, x: T)
  ensures |s + [x]| == |s| + 1
{
  assert |s + [x]| == |s| + 1;
}

lemma IndexOfAppendLeft<T>(s: seq<T>, x: T, j: int)
  requires 0 <= j < |s|
  ensures (s + [x])[j] == s[j]
{
  assert (s + [x])[j] == s[j];
}
// </vc-helpers>

// <vc-spec>
method ElementWiseModulo(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    requires |a| > 0
    requires forall i :: 0 <= i < |b| ==> b[i] != 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] % b[i]
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var res: seq<int> := [];
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == a[j] % b[j]
    invariant |a| == |b|
    invariant forall k :: 0 <= k < |b| ==> b[k] != 0
    decreases |a| - i
  {
    res := res + [a[i] % b[i]];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
