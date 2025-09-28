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
  /* code modified by LLM (iteration 2): implemented loop with invariants to find and copy common prefix */
  var minLen := if str1.Length < str2.Length then str1.Length else str2.Length;
  var i := 0;
  while i < minLen
    invariant 0 <= i <= minLen
    invariant forall k :: 0 <= k < i ==> str1[k] == str2[k]
  {
    if str1[i] != str2[i] {
      break;
    }
    i := i + 1;
  }
  result := new char[i];
  var j := 0;
  while j < i
    invariant 0 <= j <= i
    invariant forall k :: 0 <= k < i ==> str1[k] == str2[k]
    invariant forall k :: 0 <= k < j ==> result[k] == str1[k] && result[k] == str2[k]
  {
    result[j] := str1[j];
    j := j + 1;
  }
}
// </vc-code>
