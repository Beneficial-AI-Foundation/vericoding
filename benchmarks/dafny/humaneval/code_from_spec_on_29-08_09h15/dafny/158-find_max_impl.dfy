

// <vc-helpers>
function unique_chars(s: string): set<char>
{
    set c | c in s
}

lemma UniqueCharsSubset(s1: string, s2: string)
    requires s1 <= s2
    ensures unique_chars(s1) <= unique_chars(s2)
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def find_max(words: List String) -> String
Write a function that accepts a list of strings. The list contains different words. Return the word with maximum number of unique characters. If multiple strings have maximum number of unique characters, return the one which comes first in lexicographical order.
*/
// </vc-description>

// <vc-spec>
method find_max(strings : seq<string>) returns (s : string)
   // pre-conditions-start
    requires |strings| > 0
    // pre-conditions-end
    // post-conditions-start
    ensures s in strings
    ensures forall i : int :: 0 <= i < |strings| ==> |set c | c in s| >= |set c | c in strings[i]|
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    s := strings[0];
    var max_unique := |unique_chars(s)|;
    
    for i := 1 to |strings|
        invariant s in strings
        invariant max_unique == |unique_chars(s)|
        invariant forall j : int :: 0 <= j < i ==> |unique_chars(s)| >= |unique_chars(strings[j])|
        invariant forall j : int :: 0 <= j < i && |unique_chars(strings[j])| == max_unique ==> s <= strings[j]
    {
        var current_unique := |unique_chars(strings[i])|;
        
        if current_unique > max_unique {
            s := strings[i];
            max_unique := current_unique;
        } else if current_unique == max_unique && strings[i] < s {
            s := strings[i];
        }
    }
}
// </vc-code>

