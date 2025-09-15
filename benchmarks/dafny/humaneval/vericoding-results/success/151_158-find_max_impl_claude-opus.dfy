

// <vc-helpers>
function UniqueChars(s: string): set<char>
{
    set c | c in s
}

lemma UniqueCharsCorrect(s: string)
    ensures UniqueChars(s) == set c | c in s
{
}
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
    s := strings[0];
    var maxUnique := |UniqueChars(s)|;
    var i := 1;
    
    while i < |strings|
        invariant 0 <= i <= |strings|
        invariant s in strings[0..i]
        invariant maxUnique == |UniqueChars(s)|
        invariant forall j :: 0 <= j < i ==> |UniqueChars(strings[j])| <= maxUnique
    {
        var currentUnique := |UniqueChars(strings[i])|;
        if currentUnique > maxUnique {
            s := strings[i];
            maxUnique := currentUnique;
        }
        i := i + 1;
    }
    
    assert s in strings[0..|strings|];
    assert strings[0..|strings|] == strings;
}
// </vc-code>

