// <vc-helpers>
function CountUniqueChars(s: string): nat
{
  |set c | c in s|
}

function IsLexicographicallySmaller(s1: string, s2: string): bool
{
  if |s1| == 0 then |s2| > 0
  else if |s2| == 0 then false
  else if s1[0] < s2[0] then true
  else if s1[0] > s2[0] then false
  else IsLexicographicallySmaller(s1[1..], s2[1..])
}

predicate IsMaxUniqueChars(words: seq<string>, result: string)
{
  result in words &&
  forall w :: w in words ==> CountUniqueChars(result) >= CountUniqueChars(w)
}

predicate IsLexicographicallyFirst(words: seq<string>, result: string)
{
  result in words &&
  forall w :: w in words && CountUniqueChars(w) == CountUniqueChars(result) ==> 
    result == w || IsLexicographicallySmaller(result, w)
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def find_max(words: List String) -> String
Write a function that accepts a list of strings. The list contains different words. Return the word with maximum number of unique characters. If multiple strings have maximum number of unique characters, return the one which comes first in lexicographical order.
*/
// </vc-description>

// <vc-spec>
method FindMax(words: seq<string>) returns (result: string)
  requires |words| > 0
  ensures IsMaxUniqueChars(words, result)
  ensures IsLexicographicallyFirst(words, result)
// </vc-spec>
// <vc-code>
{
  result := words[0];
  var maxCount := CountUniqueChars(words[0]);
  
  for i := 1 to |words|
    invariant 0 <= i <= |words|
    invariant result in words[..i]
    invariant maxCount == CountUniqueChars(result)
    invariant forall j :: 0 <= j < i ==> CountUniqueChars(words[j]) <= maxCount
    invariant forall j :: 0 <= j < i && CountUniqueChars(words[j]) == maxCount ==> 
      result == words[j] || IsLexicographicallySmaller(result, words[j])
  {
    var currentCount := CountUniqueChars(words[i]);
    if currentCount > maxCount {
      result := words[i];
      maxCount := currentCount;
    } else if currentCount == maxCount && (result == words[i] || IsLexicographicallySmaller(words[i], result)) {
      result := words[i];
    }
  }
}
// </vc-code>
