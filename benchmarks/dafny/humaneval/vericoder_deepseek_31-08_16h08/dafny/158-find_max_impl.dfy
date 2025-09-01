

// <vc-helpers>
lemma CountUniqueCharsLemma(s: string, t: string)
    ensures |set c | c in s| >= |set c | c in t| ==> |set c | c in s| >= |set c | c in t|
{
}

lemma UniqueCharsTransitivity(s: string, t: string, u: string)
    requires |set c | c in s| >= |set c | c in t|
    requires |set c | c in t| >= |set c | c in u|
    ensures |set c | c in s| >= |set c | c in u|
{
}

function CountUniqueChars(s: string) : int
{
    |set c | c in s|
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
    var idx := 0;
    s := strings[0];
    
    while idx < |strings|
        invariant 0 <= idx <= |strings|
        invariant s in strings
        invariant forall i : int :: 0 <= i < idx ==> CountUniqueChars(s) >= CountUniqueChars(strings[i])
    {
        if CountUniqueChars(strings[idx]) > CountUniqueChars(s) {
            s := strings[idx];
        }
        idx := idx + 1;
    }
}
// </vc-code>

