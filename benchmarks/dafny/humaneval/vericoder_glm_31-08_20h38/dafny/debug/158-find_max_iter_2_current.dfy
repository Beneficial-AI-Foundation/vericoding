

// <vc-helpers>
function set_of_chars(s: string): set<char>
{
    set c | c in s :: c
}

lemma size_of_set_of_chars_is_at_least_one(s: string)
    requires |s| > 0
    ensures |set_of_chars(s)| >= 1
{
    var first := s[0];
    assert first in set_of_chars(s);
}

lemma set_of_chars_property(s: string, c: char)
    ensures c in set_of_chars(s) <==> c in s
{
}

 lemma max_string_exists(strings: seq<string>) returns (max_string: string)
    requires |strings| > 0
    ensures max_string in strings
    ensures forall i: int :: 0 <= i < |strings| ==> |set_of_chars(max_string)| >= |set_of_chars(strings[i])|
{
    max_string := strings[0];
    var i := 1;
    while i < |strings|
        invariant 0 <= i <= |strings|
        invariant max_string in strings[..i]
        invariant forall j: int :: 0 <= j < i ==> |set_of_chars(max_string)| >= |set_of_chars(strings[j])|
    {
        if |set_of_chars(strings[i])| > |set_of_chars(max_string)| {
            max_string := strings[i];
        }
        i := i + 1;
    }
}
// </vc-helpers>
// </vc-helpers>

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
    var max_str := strings[0];
    var i := 1;
    while i < |strings|
        invariant 0 <= i <= |strings|
        invariant max_str in strings[..i]
        invariant forall j: int :: 0 <= j < i ==> |set c | c in max_str| >= |set c | c in strings[j]|
    {
        if |set c | c in strings[i]| > |set c | c in max_str| {
            max_str := strings[i];
        }
        i := i + 1;
    }
    return max_str;
}
// </vc-code>
// </vc-code>

