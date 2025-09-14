// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Min(a: int, b: int): int { if a < b then a else b }
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
  var i := 0;
  while i < str1.Length && i < str2.Length && str1[i] == str2[i]
    invariant 0 <= i <= str1.Length && 0 <= i <= str2.Length
    invariant forall k :: 0 <= k < i ==> str1[k] == str2[k]
  {
    i := i + 1;
  }
  var len := i;
  result := new char[len];
  var j := 0;
  while j < len
    invariant 0 <= j <= len
    invariant forall k :: 0 <= k < j ==> result[k] == str1[k] && result[k] == str2[k]
  {
    result[j] := str1[j];
    j := j + 1;
  }
}
// </vc-code>
