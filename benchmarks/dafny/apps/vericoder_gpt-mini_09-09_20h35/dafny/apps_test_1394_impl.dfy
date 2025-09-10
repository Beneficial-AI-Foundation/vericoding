function CountAs(s: string): int
    ensures 0 <= CountAs(s) <= |s|
    ensures CountAs(s) == |s| ==> (forall i :: 0 <= i < |s| ==> s[i] == 'a')
{
    if |s| == 0 then 0
    else if s[0] == 'a' then 1 + CountAs(s[1..])
    else CountAs(s[1..])
}

function RemoveAs(s: string): string
    ensures |RemoveAs(s)| <= |s|
    ensures |RemoveAs(s)| == |s| - CountAs(s)
    ensures forall i :: 0 <= i < |RemoveAs(s)| ==> RemoveAs(s)[i] != 'a'
{
    if |s| == 0 then ""
    else if s[0] == 'a' then RemoveAs(s[1..])
    else [s[0]] + RemoveAs(s[1..])
}

// <vc-helpers>
lemma PrefixSuffixConcat(s: string, k: int)
  requires 0 <= k <= |s|
  ensures s[..k] + s[k..] == s
  decreases |s|
{
  if |s| == 0 {
    assert k == 0;
    assert s[..k] + s[k..] == "" + "";
    assert s == "";
  } else {
    if k == 0 {
      assert s[..0] + s[0..] == "" + s;
    } else {
      var c := s[0];
      PrefixSuffixConcat(s[1..], k-1);
      assert s[..k] == [c] + s[1..k];
      assert s[k..] == s[1..][k-1..];
      assert s[..k] + s[k..] == [c] + (s[1..k] + s[1..][k-1..]);
      assert s[1..k] + s[1..][k-1..] == s[1..];
      assert [c] + s[1..] == s;
    }
  }
  assert s[..k] + s[k..] == s;
}
// </vc-helpers>

// <vc-spec>
method solve(t: string) returns (result: string)
    requires |t| >= 1
    ensures result == ":(" || (|result| <= |t| && t == result + RemoveAs(result))
    ensures result != ":(" ==> (
        var z := CountAs(t);
        var nonACount := |t| - z;
        nonACount % 2 == 0 &&
        var q := nonACount / 2;
        var sLength := q + z;
        sLength <= |t| &&
        result == t[..sLength] &&
        RemoveAs(result) == t[sLength..]
    )
// </vc-spec>
// <vc-code>
{
  var z := CountAs(t);
  var nonACount := |t| - z;
  if nonACount % 2 == 1 {
    return ":(";
  }
  var q := nonACount / 2;
  var sLength := q + z;
  if sLength > |t| {
    return ":(";
  }
  var prefix := t[..sLength];
  if RemoveAs(prefix) == t[sLength..] {
    PrefixSuffixConcat(t, sLength);
    assert t == prefix + t[sLength..];
    assert RemoveAs(prefix) == t[sLength..];
    assert t == prefix + RemoveAs(prefix);
    return prefix;
  } else {
    return ":(";
  }
}
// </vc-code>

