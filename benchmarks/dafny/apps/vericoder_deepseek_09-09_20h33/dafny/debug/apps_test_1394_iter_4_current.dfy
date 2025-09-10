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
lemma {:induction true} RemoveAsLemma(s: string, start: int)
    requires 0 <= start <= |s|
    ensures RemoveAs(s[start..]) == RemoveAs(s)[start..]
    decreases |s| - start
{
    if start < |s| {
        RemoveAsLemma(s, start+1);
    } else {
        // Base case: start == |s|
        assert s[start..] == "";
        assert RemoveAs(s)[start..] == "";
    }
}

lemma CountAsConcat(s1: string, s2: string)
    ensures CountAs(s1 + s2) == CountAs(s1) + CountAs(s2)
    decreases |s1|
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
        assert CountAs(s1) == 0;
    } else {
        if s1[0] == 'a' {
            calc {
                CountAs(s1 + s2);
                1 + CountAs(s1[1..] + s2);
                == { CountAsConcat(s1[1..], s2); }
                1 + (CountAs(s1[1..]) + CountAs(s2));
                == 
                (1 + CountAs(s1[1..])) + CountAs(s2);
                == { assert CountAs(s1) == 1 + CountAs(s1[1..]); }
                CountAs(s1) + CountAs(s2);
            }
        } else {
            calc {
                CountAs(s1 + s2);
                CountAs(s1[1..] + s2);
                == { CountAsConcat(s1[1..], s2); }
                CountAs(s1[1..]) + CountAs(s2);
                == { assert CountAs(s1) == CountAs(s1[1..]); }
                CountAs(s1) + CountAs(s2);
            }
        }
    }
}

lemma RemoveAsConcat(s1: string, s2: string)
    ensures RemoveAs(s1 + s2) == RemoveAs(s1) + RemoveAs(s2)
    decreases |s1|
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
        assert RemoveAs(s1) == "";
    } else {
        RemoveAsConcat(s1[1..], s2);
        if s1[0] == 'a' {
            calc {
                RemoveAs(s1 + s2);
                == { assert s1 + s2 == [s1[0]] + (s1[1..] + s2); }
                RemoveAs([s1[0]] + (s1[1..] + s2));
                == { assert s1[0] == 'a'; }
                RemoveAs(s1[1..] + s2);
                == { RemoveAsConcat(s1[1..], s2); }
                RemoveAs(s1[1..]) + RemoveAs(s2);
                == { assert RemoveAs(s1) == RemoveAs(s1[1..]); }
                RemoveAs(s1) + RemoveAs(s2);
            }
        } else {
            calc {
                RemoveAs(s1 + s2);
                == { assert s1 + s2 == [s1[0]] + (s1[1..] + s2); }
                RemoveAs([s1[0]] + (s1[1..] + s2));
                == { assert s1[0] != 'a'; }
                [s1[0]] + RemoveAs(s1[1..] + s2);
                == { RemoveAsConcat(s1[1..], s2); }
                [s1[0]] + (RemoveAs(s1[1..]) + RemoveAs(s2));
                == 
                ([s1[0]] + RemoveAs(s1[1..])) + RemoveAs(s2);
                == { assert RemoveAs(s1) == [s1[0]] + RemoveAs(s1[1..]); }
                RemoveAs(s1) + RemoveAs(s2);
            }
        }
    }
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
    calc {
        CountAs(s[..n] + s[n..]);
        == { CountAsConcat(s[..n], s[n..]); }
        CountAs(s[..n]) + CountAs(s[n..]);
        == { assert s[..n] + s[n..] == s; }
        CountAs(s);
    }
}

lemma RemoveAsSlice(s: string, n: int)
    requires 0 <= n <= |s|
    ensures RemoveAs(s[..n]) + RemoveAs(s[n..]) == RemoveAs(s)
{
    calc {
        RemoveAs(s[..n] + s[n..]);
        == { RemoveAsConcat(s[..n], s[n..]); }
        RemoveAs(s[..n]) + RemoveAs(s[n..]);
        == { assert s[..n] + s[n..] == s; }
        RemoveAs(s);
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
        result := ":(";
    } else {
        var q := nonACount / 2;
        var sLength := q + z;
        if sLength > |t| {
            result := ":(";
        } else {
            var prefix := t[..sLength];
            var suffix := t[sLength..];
            CountAsSlice(t, sLength);
            RemoveAsSlice(t, sLength);
            assert RemoveAs(t) == RemoveAs(prefix) + RemoveAs(suffix);
            
            // Fix: Use RemoveAsLemma to prove RemoveAs(prefix) == RemoveAs(t)[..|prefix|]
            RemoveAsLemma(t, sLength);
            assert RemoveAs(t[sLength..]) == RemoveAs(t)[sLength..];
            assert RemoveAs(suffix) == RemoveAs(t)[sLength..];
            
            // Additional lemma call to relate RemoveAs(prefix) and RemoveAs(t)[..sLength]
            assert RemoveAs(prefix) == RemoveAs(t[..sLength]);
            assert RemoveAs(t) == RemoveAs(prefix) + RemoveAs(suffix);
            assert RemoveAs(t) == RemoveAs(prefix) + RemoveAs(t)[sLength..];
            
            if RemoveAs(prefix) == suffix {
                result := prefix;
            } else {
                result := ":(";
            }
        }
    }
}
// </vc-code>

