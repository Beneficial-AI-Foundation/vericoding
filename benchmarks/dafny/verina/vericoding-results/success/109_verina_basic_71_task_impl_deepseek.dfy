// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed ArrayBoundsLemma to not require preconditions since it's used in proof contexts */ function min(a: int, b: int): int { if a < b then a else b }
function {:opaque} ArrayBoundsCheck(arr: array<char>, index: int): bool { 0 <= index < arr.Length }
lemma ArrayBoundsLemma(arr: array<char>, index: int)
  ensures ArrayBoundsCheck(arr, index) == (0 <= index < arr.Length) {
  reveal ArrayBoundsCheck();
}
lemma RevealArrayBoundsCheck(arr: array<char>, index: int)
  ensures ArrayBoundsCheck(arr, index) == (0 <= index < arr.Length) {
  reveal ArrayBoundsCheck();
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
/* code modified by LLM (iteration 5): simplified implementation with proper array bounds checking */ {
  var i := 0;
  while i < str1.Length && i < str2.Length && str1[i] == str2[i]
      invariant 0 <= i <= str1.Length && i <= str2.Length
      invariant forall j :: 0 <= j < i ==> str1[j] == str2[j]
      decreases min(str1.Length, str2.Length) - i
  {
      i := i + 1;
  }
  result := new char[i];
  var j := 0;
  while j < i
      invariant 0 <= j <= i
      invariant forall k :: 0 <= k < j ==> result[k] == str1[k]
      decreases i - j
  {
      result[j] := str1[j];
      j := j + 1;
  }
}
// </vc-code>
