// <vc-preamble>
function is_alpha(c: char) : bool {
  'a' <= c <= 'z' || 'A' <= c <= 'Z'
}
function flip_case(c: char): (flipped: char)
  requires is_alpha(c)
  ensures is_alpha(flipped)
{
  if 'a' <= c <= 'z' then c - 'a' + 'A' else c - 'A' + 'a'
}
// </vc-preamble>

// <vc-helpers>
predicate AllNonAlpha(s: string)
{
  forall i :: 0 <= i < |s| ==> !is_alpha(s[i])
}

predicate HasAlpha(s: string)
{
  exists i :: 0 <= i < |s| && is_alpha(s[i])
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (t: string)

  ensures |s| == |t|
  ensures (forall i :: 0 <= i < |s| ==> !is_alpha(s[i])) ==> (forall i :: 0 <= i < |s| ==> s[i] == t[|t| - 1 - i])
  ensures (exists i :: 0 <= i < |s| && is_alpha(s[i])) ==> 
    (forall i :: 0 <= i < |t| ==> if is_alpha(s[i]) then t[i] == flip_case(s[i]) else t[i] == s[i])
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  var hasAlpha := false;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant hasAlpha ==> (exists j :: 0 <= j < i && is_alpha(s[j]))
    invariant !hasAlpha ==> (forall j :: 0 <= j < i ==> !is_alpha(s[j]))
  {
    if is_alpha(s[i]) {
      hasAlpha := true;
    }
    i := i + 1;
  }
  var b := new char[n];
  if hasAlpha {
    var k := 0;
    while k < n
      invariant 0 <= k <= n
      invariant forall j :: 0 <= j < k ==> (if is_alpha(s[j]) then b[j] == flip_case(s[j]) else b[j] == s[j])
    {
      if is_alpha(s[k]) {
        b[k] := flip_case(s[k]);
      } else {
        b[k] := s[k];
      }
      k := k + 1;
    }
    t := b[..];
    assert forall i :: 0 <= i < |t| ==> (if is_alpha(s[i]) then t[i] == flip_case(s[i]) else t[i] == s[i]);
  } else {
    var k := 0;
    while k < n
      invariant 0 <= k <= n
      invariant forall j :: 0 <= j < k ==> b[n - 1 - j] == s[j]
    {
      assert 0 <= n - 1 - k < n;
      b[n - 1 - k] := s[k];
      k := k + 1;
    }
    t := b[..];
    assert forall i :: 0 <= i < |s| ==> s[i] == t[|t| - 1 - i];
  }
}
// </vc-code>
