// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-description>
/*
function_signature: def remove_vowels(string: str) -> string
remove_vowels is a function that takes string and returns string without vowels.
*/
// </vc-description>

// <vc-spec>
method RemoveVowels(s: string) returns (result: string)
  ensures forall i :: 0 <= i < |result| ==> result[i] !in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
  ensures |result| <= |s|
// </vc-spec>
// <vc-code>
{
  result := "";
  for i := 0 to |s|
    invariant |result| <= i
    invariant forall k :: 0 <= k < |result| ==> result[k] !in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
  {
    if s[i] !in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'} {
      result := result + [s[i]];
    }
  }
}
// </vc-code>
