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
lemma CountAsPrefix(s: string, i: int)
    requires 0 <= i <= |s|
    ensures CountAs(s[..i]) <= CountAs(s)
{
    if i == 0 {
    } else if i == |s| {
    } else {
        CountAsPrefix(s, i+1);
    }
}

lemma RemoveAsPrefix(s: string, i: int)
    requires 0 <= i <= |s|
    ensures RemoveAs(s[..i]) == RemoveAs(s)[..|RemoveAs(s[..i])|]
{
    if i == 0 {
    } else {
        RemoveAsPrefix(s, i-1);
        if s[i-1] == 'a' {
        } else {
        }
    }
}

lemma RemoveAsSuffix(s: string, i: int)
    requires 0 <= i <= |s|
    ensures RemoveAs(s[i..]) == RemoveAs(s)[|RemoveAs(s[..i])|..]
{
    RemoveAsPrefix(s, i);
    assert RemoveAs(s) == RemoveAs(s[..i]) + RemoveAs(s[i..]);
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
    
    result := t[..sLength];
    
    RemoveAsSuffix(t, sLength);
}
// </vc-code>

