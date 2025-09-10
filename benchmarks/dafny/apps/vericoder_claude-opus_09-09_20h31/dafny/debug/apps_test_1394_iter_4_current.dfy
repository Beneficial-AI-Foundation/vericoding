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
        
        // Key observation: s[..i] == s[..i-1] + [s[i-1]]
        assert s[..i][..i-1] == s[..i-1];
        SlicePropertyHelper(s, i);
        
        if s[i-1] == 'a' {
            CountAsSliceProperty(s, i);
            assert CountAs(s[..i]) == CountAs(s[..i-1]) + 1;
            assert CountNonAs(s[..i]) == |s[..i]| - CountAs(s[..i]);
            assert CountNonAs(s[..i]) == i - (CountAs(s[..i-1]) + 1);
            assert CountNonAs(s[..i]) == CountNonAs(s[..i-1]);
            
            RemoveAsSlicePropertyA(s, i);
            assert RemoveAs(s[..i]) == RemoveAs(s[..i-1]);
            assert RemoveAs(s[..i]) == RemoveAs(s)[..CountNonAs(s[..i])];
        } else {
            CountAsSliceProperty(s, i);
            assert CountAs(s[..i]) == CountAs(s[..i-1]);
            assert CountNonAs(s[..i]) == |s[..i]| - CountAs(s[..i]);
            assert CountNonAs(s[..i]) == i - CountAs(s[..i-1]);
            assert CountNonAs(s[..i]) == CountNonAs(s[..i-1]) + 1;
            
            RemoveAsLengthProperty(s, i);
            assert CountNonAs(s[..i]) <= |RemoveAs(s)|;
            
            RemoveAsSlicePropertyNonA(s, i);
            assert RemoveAs(s[..i]) == RemoveAs(s[..i-1]) + [s[i-1]];
            
            RemoveAsIndexProperty(s, i);
            assert RemoveAs(s)[CountNonAs(s[..i-1])] == s[i-1];
            assert RemoveAs(s[..i]) == RemoveAs(s)[..CountNonAs(s[..i])];
        }
    }
}

lemma SlicePropertyHelper(s: string, i: int)
    requires 0 < i <= |s|
    ensures s[..i] == s[..i-1] + [s[i-1]]
{
    // This is a basic property of string slicing
}

lemma CountAsSliceProperty(s: string, i: int)
    requires 0 < i <= |s|
    ensures s[i-1] == 'a' ==> CountAs(s[..i]) == CountAs(s[..i-1]) + 1
    ensures s[i-1] != 'a' ==> CountAs(s[..i]) == CountAs(s[..i-1])
{
    SlicePropertyHelper(s, i);
    var prefix := s[..i-1];
    var last := [s[i-1]];
    assert s[..i] == prefix + last;
    
    CountAsConcat(prefix, last);
    
    if s[i-1] == 'a' {
        assert CountAs(last) == 1;
        assert CountAs(s[..i]) == CountAs(prefix) + 1;
        assert CountAs(s[..i]) == CountAs(s[..i-1]) + 1;
    } else {
        assert CountAs(last) == 0;
        assert CountAs(s[..i]) == CountAs(prefix);
        assert CountAs(s[..i]) == CountAs(s[..i-1]);
    }
}

lemma CountAsConcat(s1: string, s2: string)
    ensures CountAs(s1 + s2) == CountAs(s1) + CountAs(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        CountAsConcat(s1[1..], s2);
        assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
        if s1[0] == 'a' {
            calc == {
                CountAs(s1 + s2);
                1 + CountAs((s1 + s2)[1..]);
                1 + CountAs(s1[1..] + s2);
                1 + CountAs(s1[1..]) + CountAs(s2);
                CountAs(s1) + CountAs(s2);
            }
        } else {
            calc == {
                CountAs(s1 + s2);
                CountAs((s1 + s2)[1..]);
                CountAs(s1[1..] + s2);
                CountAs(s1[1..]) + CountAs(s2);
                CountAs(s1) + CountAs(s2);
            }
        }
    }
}

lemma RemoveAsConcat(s1: string, s2: string)
    ensures RemoveAs(s1 + s2) == RemoveAs(s1) + RemoveAs(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        RemoveAsConcat(s1[1..], s2);
        assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
        if s1[0] == 'a' {
            calc == {
                RemoveAs(s1 + s2);
                RemoveAs((s1 + s2)[1..]);
                RemoveAs(s1[1..] + s2);
                RemoveAs(s1[1..]) + RemoveAs(s2);
                RemoveAs(s1) + RemoveAs(s2);
            }
        } else {
            calc == {
                RemoveAs(s1 + s2);
                [s1[0]] + RemoveAs((s1 + s2)[1..]);
                [s1[0]] + RemoveAs(s1[1..] + s2);
                [s1[0]] + RemoveAs(s1[1..]) + RemoveAs(s2);
                RemoveAs(s1) + RemoveAs(s2);
            }
        }
    }
}

lemma RemoveAsSlicePropertyA(s: string, i: int)
    requires 0 < i <= |s|
    requires s[i-1] == 'a'
    ensures RemoveAs(s[..i]) == RemoveAs(s[..i-1])
{
    SlicePropertyHelper(s, i);
    var prefix := s[..i-1];
    var last := [s[i-1]];
    assert s[..i] == prefix + last;
    assert last == ['a'];
    
    RemoveAsConcat(prefix, last);
    assert RemoveAs(last) == "";
    assert RemoveAs(s[..i]) == RemoveAs(prefix) + "";
    assert RemoveAs(s[..i]) == RemoveAs(s[..i-1]);
}

lemma RemoveAsSlicePropertyNonA(s: string, i: int)
    requires 0 < i <= |s|
    requires s[i-1] != 'a'
    ensures RemoveAs(s[..i]) == RemoveAs(s[..i-1]) + [s[i-1]]
{
    SlicePropertyHelper(s, i);
    var prefix := s[..i-1];
    var last := [s[i-1]];
    assert s[..i] == prefix + last;
    
    RemoveAsConcat(prefix, last);
    assert RemoveAs(last) == [s[i-1]];
    assert RemoveAs(s[..i]) == RemoveAs(prefix) + [s[i-1]];
    assert RemoveAs(s[..i]) == RemoveAs(s[..i-1]) + [s[i-1]];
}

lemma RemoveAsIndexProperty(s: string, i: int)
    requires 0 < i <= |s|
    requires s[i-1] != 'a'
    requires CountNonAs(s[..i-1]) < |RemoveAs(s)|
    ensures RemoveAs(s)[CountNonAs(s[..i-1])] == s[i-1]
{
    RemoveAsStructure(s, i);
}

lemma RemoveAsStructure(s: string, i: int)
    requires 0 < i <= |s|
    requires s[i-1] != 'a'
    requires CountNonAs(s[..i-1]) < |RemoveAs(s)|
    ensures RemoveAs(s)[CountNonAs(s[..i-1])] == s[i-1]
{
    var prefix := s[..i];
    var suffix := s[i..];
    assert s == prefix + suffix;
    
    RemoveAsConcat(prefix, suffix);
    assert RemoveAs(s) == RemoveAs(prefix) + RemoveAs(suffix);
    
    RemoveAsSlicePropertyNonA(s, i);
    assert RemoveAs(prefix) == RemoveAs(s[..i-1]) + [s[i-1]];
    
    assert |RemoveAs(s[..i-1])| == CountNonAs(s[..i-1]);
    assert |RemoveAs(prefix)| == |RemoveAs(s[..i-1])| + 1;
    assert |RemoveAs(prefix)| == CountNonAs(s[..i-1]) + 1;
    
    assert RemoveAs(s)[CountNonAs(s[..i-1])] == RemoveAs(prefix)[|RemoveAs(s[..i-1])|];
    assert RemoveAs(prefix)[|RemoveAs(s[..i-1])|] == s[i-1];
}

lemma RemoveAsLengthProperty(s: string, i: int)
    requires 0 < i <= |s|
    requires s[i-1] != 'a'
    ensures CountNonAs(s[..i]) <= |RemoveAs(s)|
{
    assert CountNonAs(s[..i]) == |s[..i]| - CountAs(s[..i]);
    assert |RemoveAs(s)| == |s| - CountAs(s);
    CountAsMonotonic(s, i);
    assert CountAs(s[..i]) <= CountAs(s);
    assert CountNonAs(s[..i]) <= |RemoveAs(s)|;
}

lemma CountAsMonotonic(s: string, i: int)
    requires 0 <= i <= |s|
    ensures CountAs(s[..i]) <= CountAs(s)
{
    if i == 0 {
        assert CountAs(s[..0]) == 0;
    } else if i == |s| {
        assert s[..i] == s;
    } else {
        var prefix := s[..i];
        var suffix := s[i..];
        assert s == prefix + suffix;
        CountAsConcat(prefix, suffix);
        assert CountAs(s) == CountAs(prefix) + CountAs(suffix);
        assert CountAs(suffix) >= 0;
        assert CountAs(s[..i]) <= CountAs(s);
    }
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

