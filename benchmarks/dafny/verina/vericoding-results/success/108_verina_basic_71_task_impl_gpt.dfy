// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function minInt(a: int, b: int): int { if a < b then a else b }
predicate PrefixEqual(a: array<char>, b: array<char>, n: int)
  reads a, b
{
  0 <= n <= a.Length && n <= b.Length &&
  (forall i :: 0 <= i < n ==> a[i] == b[i])
}
// </vc-helpers>

// <vc-spec>
method LongestCommonPrefix(str1: array<char>, str2: array<char>) returns (result: array<char>)
    ensures
        result.Length <= str1.Length &&
        result.Length <= str2.Length &&
        (forall i :: 0 <= i < result.Length ==> result[i] == str1[i] && result[i] == str2[i]) &&
        (result.Length == str1.Length || result.Length == str2.Length || 
            (result.Length < str1.Length && result.Length < str2.Length && str1[result.Length] != str2[result.Length]))
// </vc-spec>
// <vc-code>
{
  var i: int := 0;
  while i < str1.Length && i < str2.Length && str1[i] == str2[i]
    invariant 0 <= i <= str1.Length
    invariant 0 <= i <= str2.Length
    invariant forall j :: 0 <= j < i ==> str1[j] == str2[j]
    decreases str1.Length + str2.Length - i
  {
    i := i + 1;
  }
  result := new char[i];
  var j: int := 0;
  while j < i
    invariant 0 <= j <= i
    invariant i <= str1.Length && i <= str2.Length
    invariant forall k :: 0 <= k < j ==> result[k] == str1[k] && result[k] == str2[k]
    decreases i - j
  {
    result[j] := str1[j];
    assert str1[j] == str2[j];
    j := j + 1;
  }
  if i < str1.Length && i < str2.Length {
    assert str1[i] != str2[i];
  }
}
// </vc-code>
