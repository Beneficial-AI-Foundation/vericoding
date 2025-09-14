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
lemma SplitConcat(s: string, k: int)
  requires 0 <= k <= |s|
  ensures s == s[..k] + s[k..]
{
  assert |s[..k]| == k;
  assert |s[k..]| == |s| - k;
  assert |s[..k] + s[k..]| == |s|;

  forall i | 0 <= i < |s|
    ensures (s[..k] + s[k..])[i] == s[i]
  {
    if i < k {
      assert (s[..k] + s[k..])[i] == s[..k][i];
      assert s[..k][i] == s[i];
    } else {
      assert 0 <= i - k;
      assert |s[k..]| == |s| - k;
      assert i - k < |s| - k;
      assert i - k < |s[k..]|;
      assert (s[..k] + s[k..])[i] == s[k..][i - k];
      assert s[k..][i - k] == s[k + (i - k)];
      assert s[k + (i - k)] == s[i];
    }
  }
  assert s == s[..k] + s[k..];
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
  var nonA := |t| - z;
  if nonA % 2 != 0 {
    result := ":(";
    return;
  }
  var q := nonA / 2;
  var sLen := q + z;
  if sLen > |t| {
    result := ":(";
    return;
  }
  var s := t[..sLen];
  if RemoveAs(s) == t[sLen..] {
    result := s;
    calc {
      t;
      == { SplitConcat(t, sLen); }
      t[..sLen] + t[sLen..];
      == { assert result == t[..sLen]; assert RemoveAs(result) == t[sLen..]; }
      result + RemoveAs(result);
    }
  } else {
    result := ":(";
  }
}
// </vc-code>

