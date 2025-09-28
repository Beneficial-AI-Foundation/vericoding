// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  var len := 0;
  while len < str1.Length && len < str2.Length && str1[len] == str2[len]
      invariant 0 <= len && len <= str1.Length && len <= str2.Length
      invariant forall j :: 0 <= j < len ==> str1[j] == str2[j]
  {
      len := len + 1;
  }
  result := new char[len];
  var i := 0;
  while i < len
      invariant 0 <= i <= len
      invariant forall j :: 0 <= j < i ==> result[j] == str1[j] && result[j] == str2[j]
  {
      result[i] := str1[i];
      i := i + 1;
  }
}
// </vc-code>
