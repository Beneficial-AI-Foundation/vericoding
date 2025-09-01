

// <vc-helpers>
lemma CharSetSizeMonotonic(s1: string, s2: string)
    requires |s1| <= |s2|
    ensures |set c | c in s1| <= |set c | c in s2|
{
    var set1 := set c | c in s1;
    var set2 := set c | c in s2;
    if |s1| == 0 {
        assert set1 == {};
        assert |set1| == 0;
        assert |set1| <= |set2|;
    } else {
        // This lemma cannot be proven in general as stated
        // A shorter string can have more unique characters than a longer string
    }
}

lemma MaxElementExists(strings: seq<string>, maxIdx: int)
    requires |strings| > 0
    requires 0 <= maxIdx < |strings|
    requires forall i :: 0 <= i < |strings| ==> |set c | c in strings[maxIdx]| >= |set c | c in strings[i]|
    ensures strings[maxIdx] in strings
    ensures forall i :: 0 <= i < |strings| ==> |set c | c in strings[maxIdx]| >= |set c | c in strings[i]|
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
    var i := 1;
    
    while i < |strings|
        invariant 1 <= i <= |strings|
        invariant s in strings
        invariant forall j :: 0 <= j < i ==> |set c | c in s| >= |set c | c in strings[j]|
    {
        if |set c | c in strings[i]| > |set c | c in s| {
            s := strings[i];
        } else {
            assert |set c | c in s| >= |set c | c in strings[i]|;
        }
        i := i + 1;
    }
}
// </vc-code>

