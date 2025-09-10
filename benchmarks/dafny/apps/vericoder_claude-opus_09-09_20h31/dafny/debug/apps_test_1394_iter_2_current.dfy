function CountAs(s: string): int
    ensures 0 <= CountAs(s) <= |s|
    ensures CountAs(s) == |s| ==> (forall i :: 0 <= i < |s| ==> s[i] == 'a')
{
    if |s| == 0 then 0
    else if s[0] == 'a' then 1 + CountAs(s[1..])
    else CountAs(s[1..])
}

function RemoveAs(s: string): string
    ensures |RemoveAs(s)| <= |s|
    ensures |RemoveAs(s)| == |s| - CountAs(s)
    ensures forall i :: 0 <= i < |RemoveAs(s)| ==> RemoveAs(s)[i] != 'a'
{
    if |s| == 0 then ""
    else if s[0] == 'a' then RemoveAs(s[1..])
    else [s[0]] + RemoveAs(s[1..])
}

// <vc-helpers>
lemma RemoveAsPrefix(s: string, i: int)
    requires 0 <= i <= |s|
    ensures CountNonAs(s[..i]) <= |RemoveAs(s)|
    ensures RemoveAs(s[..i]) == RemoveAs(s)[..CountNonAs(s[..i])]
{
    if i == 0 {
        assert s[..i] == "";
        assert RemoveAs(s[..i]) == "";
        assert CountNonAs(s[..i]) == 0;
        assert RemoveAs(s)[..0] == "";
    } else {
        RemoveAsPrefix(s, i-1);
        assert CountNonAs(s[..i-1]) <= |RemoveAs(s)|;
        
        if s[i-1] == 'a' {
            assert s[..i] == s[..i-1] + [s[i-1]];
            assert CountNonAs(s[..i]) == CountNonAs(s[..i-1]);
            assert RemoveAs(s[..i]) == RemoveAs(s[..i-1]);
            assert RemoveAs(s[..i]) == RemoveAs(s)[..CountNonAs(s[..i])];
        } else {
            assert s[..i] == s[..i-1] + [s[i-1]];
            assert CountNonAs(s[..i]) == CountNonAs(s[..i-1]) + 1;
            
            // Need to show that adding a non-'a' character increases RemoveAs length
            RemoveAsLengthProperty(s, i);
            assert CountNonAs(s[..i]) <= |RemoveAs(s)|;
            
            assert RemoveAs(s[..i]) == RemoveAs(s[..i-1]) + [s[i-1]];
            assert RemoveAs(s[..i]) == RemoveAs(s)[..CountNonAs(s[..i-1])] + [s[i-1]];
            assert RemoveAs(s)[CountNonAs(s[..i-1])] == s[i-1];
            assert RemoveAs(s[..i]) == RemoveAs(s)[..CountNonAs(s[..i])];
        }
    }
}

lemma RemoveAsLengthProperty(s: string, i: int)
    requires 0 < i <= |s|
    requires s[i-1] != 'a'
    ensures CountNonAs(s[..i]) <= |RemoveAs(s)|
{
    assert CountNonAs(s[..i]) == |s[..i]| - CountAs(s[..i]);
    assert |RemoveAs(s)| == |s| - CountAs(s);
    assert CountAs(s[..i]) <= CountAs(s);
    assert CountNonAs(s[..i]) <= |RemoveAs(s)|;
}

function CountNonAs(s: string): int
    ensures CountNonAs(s) == |s| - CountAs(s)
    ensures 0 <= CountNonAs(s) <= |s|
{
    |s| - CountAs(s)
}

lemma VerifyRemoveAsMatchesSuffix(t: string, sLength: int)
    requires 0 <= sLength <= |t|
    requires var s := t[..sLength];
             var suffix := t[sLength..];
             RemoveAs(s) == suffix
    ensures var s := t[..sLength];
            t == s + RemoveAs(s)
{
    var s := t[..sLength];
    var suffix := t[sLength..];
    assert t == s + suffix;
    assert RemoveAs(s) == suffix;
    assert t == s + RemoveAs(s);
}
// </vc-helpers>

// <vc-spec>
method solve(t: string) returns (result: string)
    requires |t| >= 1
    ensures result == ":(" || (|result| <= |t| && t == result + RemoveAs(result))
    ensures result != ":(" ==> (
        var z := CountAs(t);
        var nonACount := |t| - z;
        nonACount % 2 == 0 &&
        var q := nonACount / 2;
        var sLength := q + z;
        sLength <= |t| &&
        result == t[..sLength] &&
        RemoveAs(result) == t[sLength..]
    )
// </vc-spec>
// <vc-code>
{
    var z := CountAs(t);
    var nonACount := |t| - z;
    
    if nonACount % 2 != 0 {
        return ":(";
    }
    
    var q := nonACount / 2;
    var sLength := q + z;
    
    if sLength > |t| {
        return ":(";
    }
    
    var candidate := t[..sLength];
    var suffix := t[sLength..];
    
    if RemoveAs(candidate) == suffix {
        VerifyRemoveAsMatchesSuffix(t, sLength);
        return candidate;
    } else {
        return ":(";
    }
}
// </vc-code>

