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
lemma Div2Bounds(n: int)
  requires n >= 0
  ensures 0 <= n/2 <= n
{
  assert 0 <= n/2;
  assert n == 2*(n/2) + n%2;
  assert 0 <= n%2 < 2;
  assert 2*(n/2) <= n;
  assert n/2 <= 2*(n/2);
  assert n/2 <= n;
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
  if nonACount % 2 != 0 {
    return ":(";
  }
  assert 0 <= z <= |t|;
  assert nonACount >= 0;
  call Div2Bounds(nonACount);
  var q := nonACount / 2;
  assert 0 <= q <= nonACount;
  var sLength := q + z;
  assert sLength <= nonACount + z;
  assert nonACount + z == |t|;
  assert 0 <= sLength <= |t|;
  var s := t[..sLength];
  var u := t[sLength..];
  if RemoveAs(s) == u {
    assert s + u == t;
    result := s;
  } else {
    result := ":(";
  }
}
// </vc-code>

