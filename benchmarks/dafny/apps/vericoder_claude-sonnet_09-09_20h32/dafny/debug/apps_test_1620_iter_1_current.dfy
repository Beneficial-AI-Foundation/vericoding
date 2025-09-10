predicate ValidInput(n: int)
{
  n >= 1
}

predicate ValidOutput(s: string, n: int)
{
  |s| == n &&
  (forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b' || s[i] == 'c') &&
  (forall i :: 0 <= i <= |s| - 3 ==> !(s[i] == s[i+2]))
}

predicate MinimalCUsage(s: string)
{
  forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
}

// <vc-helpers>
lemma AlternatingPattern(s: string, n: int)
  requires n >= 1
  requires |s| == n
  requires forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
  requires forall i :: 0 <= i < |s| ==> if i % 2 == 0 then s[i] == 'a' else s[i] == 'b'
  ensures forall i :: 0 <= i <= |s| - 3 ==> !(s[i] == s[i+2])
{
  forall i | 0 <= i <= |s| - 3
    ensures !(s[i] == s[i+2])
  {
    if i % 2 == 0 {
      assert s[i] == 'a';
      assert s[i+2] == 'a';
      assert i + 2 < |s|;
      assert (i + 2) % 2 == 0;
    } else {
      assert s[i] == 'b';
      assert s[i+2] == 'b';
      assert i + 2 < |s|;
      assert (i + 2) % 2 == 1;
    }
  }
}

function BuildAlternatingString(n: int): string
  requires n >= 1
  ensures |BuildAlternatingString(n)| == n
  ensures forall i :: 0 <= i < n ==> if i % 2 == 0 then BuildAlternatingString(n)[i] == 'a' else BuildAlternatingString(n)[i] == 'b'
{
  if n == 1 then "a"
  else if n % 2 == 0 then BuildAlternatingString(n-1) + "b"
  else BuildAlternatingString(n-1) + "a"
}

lemma BuildAlternatingStringProperties(n: int)
  requires n >= 1
  ensures var s := BuildAlternatingString(n);
          |s| == n &&
          (forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b') &&
          (forall i :: 0 <= i < |s| ==> if i % 2 == 0 then s[i] == 'a' else s[i] == 'b') &&
          (forall i :: 0 <= i <= |s| - 3 ==> !(s[i] == s[i+2]))
{
  var s := BuildAlternatingString(n);
  AlternatingPattern(s, n);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: string)
  requires ValidInput(n)
  ensures ValidOutput(result, n)
  ensures MinimalCUsage(result)
// </vc-spec>
// <vc-code>
{
  result := BuildAlternatingString(n);
  BuildAlternatingStringProperties(n);
}
// </vc-code>

