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
    ensures t == s[..i] + s[i..]
    ensures RemoveAs(s) == RemoveAs(s[..i]) + RemoveAs(s[i..])
{
    if i == 0 {
    } else if i == |s| {
    } else {
        calc {
            RemoveAs(s);
            RemoveAs([s[0]] + s[1..]);
            { if s[0] == 'a' {
            } else {
            }}
            RemoveAs(s[1..]);
            { RemoveAsPrefix(s[1..], i-1); }
            RemoveAs(s[1..][..i-1]) + RemoveAs(s[1..][i-1..]);
            == RemoveAs(s[1..i]) + RemoveAs(s[i..]);
            { RemoveAsPrefix(s, 1); }
            RemoveAs(s[..1]) + RemoveAs(s[1..i]) + RemoveAs(s[i..]);
            { RemoveAsPrefix(s, i); }
            RemoveAs(s[..i]) + RemoveAs(s[i..]);
        }
    }
}

lemma CountAsAdditivity(s: string, i: int)
    requires 0 <= i <= |s|
    ensures CountAs(s) == CountAs(s[..i]) + CountAs(s[i..])
{
    if i == 0 {
    } else if i == |s| {
    } else {
        calc {
            CountAs(s);
            CountAs([s[0]] + s[1..]);
            (if s[0] == 'a' then 1 else 0) + CountAs(s[1..]);
            { CountAsAdditivity(s[1..], i-1); }
            (if s[0] == 'a' then 1 else 0) + CountAs(s[1..][..i-1]) + CountAs(s[1..][i-1..]);
            (if s[0] == 'a' then 1 else 0) + CountAs(s[1..i]) + CountAs(s[i..]);
            CalcAs(s[..1]) + CountAs(s[1..i]) + CountAs(s[i..]);
            { CountAsAdditivity(s, i); }
            CountAs(s[..i]) + CountAs(s[i..]);
        }
    }
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

    var s := t[..sLength];
    if RemoveAs(s) != t[sLength..] {
        return ":(";
    }
    return s;
}
// </vc-code>

