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
    decreases i
{
    if i == 0 {
        assert s[..i] == "";
        assert CountAs(s[..i]) == 0;
    } else if i == |s| {
        assert s[..i] == s;
    } else {
        CountAsPrefix(s, i-1);
        if s[i-1] == 'a' {
            assert s[..i] == s[..i-1] + [s[i-1]];
            assert CountAs(s[..i]) == CountAs(s[..i-1]) + 1;
        } else {
            assert s[..i] == s[..i-1] + [s[i-1]];
            assert CountAs(s[..i]) == CountAs(s[..i-1]);
        }
    }
}

lemma RemoveAsPrefix(s: string, i: int)
    requires 0 <= i <= |s|
    ensures |RemoveAs(s[..i])| <= |RemoveAs(s)|
    ensures RemoveAs(s[..i]) == RemoveAs(s)[..|RemoveAs(s[..i])|]
    decreases i
{
    if i == 0 {
        assert s[..i] == "";
        assert RemoveAs(s[..i]) == "";
    } else {
        RemoveAsPrefix(s, i-1);
        if s[i-1] == 'a' {
            assert s[..i] == s[..i-1] + [s[i-1]];
            assert RemoveAs(s[..i]) == RemoveAs(s[..i-1]);
        } else {
            assert s[..i] == s[..i-1] + [s[i-1]];
            assert RemoveAs(s[..i]) == RemoveAs(s[..i-1]) + [s[i-1]];
            assert |RemoveAs(s[..i])| == |RemoveAs(s[..i-1])| + 1;
        }
    }
}

lemma RemoveAsSuffix(s: string, i: int)
    requires 0 <= i <= |s|
    ensures |RemoveAs(s[..i])| <= |RemoveAs(s)|
    ensures |RemoveAs(s[..i])| + |RemoveAs(s[i..])| == |RemoveAs(s)|
    ensures RemoveAs(s[i..]) == RemoveAs(s)[|RemoveAs(s[..i])|..]
    ensures RemoveAs(s) == RemoveAs(s[..i]) + RemoveAs(s[i..])
{
    RemoveAsPrefix(s, i);
    if i == |s| {
        assert s[i..] == "";
        assert RemoveAs(s[i..]) == "";
        assert s[..i] == s;
    } else if i == 0 {
        assert s[..i] == "";
        assert RemoveAs(s[..i]) == "";
        assert s[i..] == s;
    } else {
        assert s == s[..i] + s[i..];
        RemoveAsConcat(s[..i], s[i..]);
    }
}

lemma RemoveAsConcat(s1: string, s2: string)
    ensures RemoveAs(s1 + s2) == RemoveAs(s1) + RemoveAs(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
        RemoveAsConcat(s1[1..], s2);
    }
}

lemma CountAsConcat(s1: string, s2: string)
    ensures CountAs(s1 + s2) == CountAs(s1) + CountAs(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
        CountAsConcat(s1[1..], s2);
    }
}

lemma RemoveAsOnlyAs(s: string)
    requires forall i :: 0 <= i < |s| ==> s[i] == 'a'
    ensures RemoveAs(s) == ""
{
    if |s| == 0 {
        assert RemoveAs(s) == "";
    } else {
        assert s[0] == 'a';
        RemoveAsOnlyAs(s[1..]);
    }
}

lemma AllAsProperty(s: string)
    requires CountAs(s) == 0
    ensures forall i :: 0 <= i < |s| ==> s[i] != 'a'
    ensures RemoveAs(s) == s
{
    if |s| == 0 {
        assert RemoveAs(s) == "";
    } else {
        assert s[0] != 'a';
        AllAsProperty(s[1..]);
        assert RemoveAs(s) == [s[0]] + RemoveAs(s[1..]);
        assert RemoveAs(s[1..]) == s[1..];
        assert RemoveAs(s) == [s[0]] + s[1..];
        assert RemoveAs(s) == s;
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
    
    result := t[..sLength];
    
    CountAsPrefix(t, sLength);
    RemoveAsSuffix(t, sLength);
    CountAsConcat(t[..sLength], t[sLength..]);
    
    assert CountAs(t) == CountAs(t[..sLength]) + CountAs(t[sLength..]);
    assert z == CountAs(result) + CountAs(t[sLength..]);
    assert |RemoveAs(result)| == |result| - CountAs(result);
    assert |RemoveAs(result)| == sLength - CountAs(result);
    assert |t[sLength..]| == |t| - sLength;
    assert |t[sLength..]| == |t| - (q + z);
    assert |t[sLength..]| == |t| - z - q;
    assert |t[sLength..]| == nonACount - q;
    assert |t[sLength..]| == q;
    
    if |t[sLength..]| == 0 {
        assert t[sLength..] == "";
        assert CountAs(t[sLength..]) == 0;
        assert RemoveAs(t[sLength..]) == "";
        assert RemoveAs(result) == t[sLength..];
    } else {
        assert |t[sLength..]| == q;
        
        if CountAs(t[sLength..]) > 0 {
            assert CountAs(t) == z + CountAs(t[sLength..]);
            assert CountAs(t) > z;
            assert |t| - CountAs(t) < |t| - z;
            assert nonACount < nonACount;
            assert false;
        }
        assert CountAs(t[sLength..]) == 0;
        
        AllAsProperty(t[sLength..]);
        assert forall i :: 0 <= i < |t[sLength..]| ==> t[sLength..][i] != 'a';
        assert RemoveAs(t[sLength..]) == t[sLength..];
        assert |RemoveAs(t[sLength..])| == |t[sLength..]|;
        assert |RemoveAs(t[sLength..])| == q;
        assert |RemoveAs(result)| == sLength - CountAs(result);
        assert sLength == q + z;
        assert CountAs(result) <= z;
        assert |RemoveAs(result)| >= q;
        assert |RemoveAs(result)| == q;
        assert RemoveAs(result) == t[sLength..];
    }
}
// </vc-code>

