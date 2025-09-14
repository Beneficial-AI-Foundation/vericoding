

// <vc-helpers>
lemma FindSublist(sub: seq<int>, main: seq<int>, i: int)
  requires 0 <= i <= |main| - |sub|
  ensures sub == main[i..i + |sub|] ==> exists i' {:trigger main[i'..i' + |sub|]} :: 0 <= i' <= |main| - |sub| && sub == main[i'..i' + |sub|]
{
}

lemma NoSublistBeforeJ(sub: seq<int>, main: seq<int>, j: int)
  requires 0 <= j <= |main| - |sub| + 1
  requires !(exists i {:trigger main[i..i + |sub|]} :: 0 <= i < j && sub == main[i..i + |sub|])
  ensures forall i :: 0 <= i < j ==> sub != main[i..i + |sub|]
{
  if j > 0 {
    var i: int := 0;
    while i < j
      invariant forall k :: 0 <= k < i ==> sub != main[k..k + |sub|]
    {
      assert sub != main[i..i + |sub|];
      i := i + 1;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures true <== (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
// </vc-spec>
// <vc-code>
{
  result := false;
  var j := 0;
  while j <= |main| - |sub|
    invariant 0 <= j <= |main| - |sub| + 1
    invariant !(exists i {:trigger main[i..i + |sub|]} :: 0 <= i < j && sub == main[i..i + |sub|])
  {
    var k := 0;
    while k < |sub| && j + k < |main| && main[j + k] == sub[k]
      invariant 0 <= k <= |sub|
      invariant forall l :: 0 <= l < k ==> main[j + l] == sub[l]
    {
      k := k + 1;
    }
    if k == |sub| {
      result := true;
      return;
    }
    j := j + 1;
  }
}
// </vc-code>

