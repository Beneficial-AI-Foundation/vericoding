Given a string t, find a string s such that when you create s' by removing all 'a' 
characters from s (keeping other characters in order) and concatenate s and s' to 
form t = s + s', output the unique string s if it exists, otherwise output ":(".

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
{
    var z := CountAs(t);
    var nonACount := |t| - z;

    if nonACount % 2 != 0 {
        result := ":(";
        return;
    }

    var q := nonACount / 2;
    var sLength := q + z;

    if sLength > |t| {
        result := ":(";
        return;
    }

    var s := t[..sLength];
    var ss := t[sLength..];
    var p := RemoveAs(s);

    if p == ss {
        result := s;
    } else {
        result := ":(";
    }
}
