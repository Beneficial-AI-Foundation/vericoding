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
lemma {:induction ""} RemoveAsLemma(s: string, start: int)
    requires 0 <= start <= |s|
    ensures RemoveAs(s[start..]) == RemoveAs(s)[start..]
    decreases |s| - start
{
    if start < |s| {
        RemoveAsLemma(s, start+1);
    }
}

lemma CountAsConcat(s1: string, s2: string)
    ensures CountAs(s1 + s2) == CountAs(s1) + CountAs(s2)
{
}

lemma RemoveAsConcat(s1: string, s2: string)
    ensures RemoveAs(s1 + s2) == RemoveAs(s1) + RemoveAs(s2)
{
}

lemma SliceProperties(s: string, n: int)
    requires 0 <= n <= |s|
    ensures |s[..n]| == n
    ensures |s[n..]| == |s| - n
{
}

lemma CountAsSlice(s: string, n: int)
    requires 0 <= n <= |s|
    ensures CountAs(s[..n]) + CountAs(s[n..]) == CountAs(s)
{
    CountAsConcat(s[..n], s[n..]);
}

lemma RemoveAsSlice(s: string, n: int)
    requires 0 <= n <= |s|
    ensures RemoveAs(s[..n]) + RemoveAs(s[n..]) == RemoveAs(s)
{
    RemoveAsConcat(s[..n], s[n..]);
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
        result := ":(";
    } else {
        var q := nonACount / 2;
        var sLength := q + z;
        if sLength > |t| {
            result := ":(";
        } else {
            var prefix := t[..sLength];
            var suffix := t[sLength..];
            if RemoveAs(prefix) == suffix {
                result := prefix;
            } else {
                result := ":(";
            }
        }
    }
}
// </vc-code>

