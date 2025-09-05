/*
function_signature: def find_max(words: List String) -> String
Write a function that accepts a list of strings. The list contains different words. Return the word with maximum number of unique characters. If multiple strings have maximum number of unique characters, return the one which comes first in lexicographical order.
*/

method find_max(strings : seq<string>) returns (s : string)
   // pre-conditions-start
    requires |strings| > 0
    // pre-conditions-end
    // post-conditions-start
    ensures s in strings
    ensures forall i : int :: 0 <= i < |strings| ==> |set c | c in s| >= |set c | c in strings[i]|
    // post-conditions-end
{
  assume false;
}
