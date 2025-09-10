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
    ensures RemoveAs(s) == RemoveAs(s[..i]) + RemoveAs(s[i..])
{
    if i == 0 {
        calc {
            RemoveAs(s);
            RemoveAs(s[..0] + s[0..]);
            RemoveAs(s);
        }
    } else if i == |s| {
        calc {
            RemoveAs(s);
            RemoveAs(s[..|s|] + s[|s|..]);
            RemoveAs(s);
        }
    } else {
        calc {
            RemoveAs(s);
            RemoveAs([s[0]] + s[1..]);
            { if s[0] == 'a' {
                calc {
                    RemoveAs([s[0]] + s[1..]);
                    RemoveAs(s[1..]);
                    RemoveAs(s[1..]) + "";
                    RemoveAs(s[1..]) + RemoveAs("");
                    RemoveAs(s[1..]) + RemoveAs(s[i..][..0]);
                }
            } else {
                calc {
                    RemoveAs([s[0]] + s[1..]);
                    [s[0]] + RemoveAs(s[1..]);
                    [s[0]] + RemoveAs(s[1..]) + "";
                    [s[0]] + RemoveAs(s[1..]) + RemoveAs("");
                    [s[0]] + RemoveAs(s[1..]) + RemoveAs(s[i..][..0]);
                }
            }}
            RemoveAs(s[1..]);
            { RemoveAsPrefix(s[1..], i-1); }
            RemoveAs(s[1..][..i-1]) + RemoveAs(s[1..][i-1..]);
            == RemoveAs(s[1..i]) + RemoveAs(s[i..]);
            { 
                if s[0] == 'a' {
                    calc {
                        RemoveAs(s[..1]) + (RemoveAs(s[1..i]) + RemoveAs(s[i..]));
                        RemoveAs("") + (RemoveAs(s[1..i]) + RemoveAs(s[i..]));
                        RemoveAs(s[1..i]) + RemoveAs(s[i..]);
                    }
                } else {
                    calc {
                        RemoveAs(s[..1]) + (RemoveAs(s[1..i]) + RemoveAs(s[i..]));
                        [s[0]] + RemoveAs("") + (RemoveAs(s[1..i]) + RemoveAs(s[i..]));
                        [s[0]] + (RemoveAs(s[1..i]) + RemoveAs(s[i..]));
                    }
                }
            }
        }
    }
}

lemma CountAsAdditivity(s: string, i: int)
    requires 0 <= i <= |s|
    ensures CountAs(s) == CountAs(s[..i]) + CountAs(s[i..])
{
    if i == 0 {
        calc {
            CountAs(s);
            CountAs(s[..0]) + CountAs(s[0..]);
        }
    } else if i == |s| {
        calc {
            CountAs(s);
            CountAs(s[..|s|]) + CountAs(s[|s|..]);
        }
    } else {
        calc {
            CountAs(s);
            CountAs([s[0]] + s[1..]);
            (if s[0] == 'a' then 1 else 0) + CountAs(s[1..]);
            { CountAsAdditivity(s[1..], i-1); }
            (if s[0] == 'a' then 1 else 0) + CountAs(s[1..][..i-1]) + CountAs(s[1..][i-1..]);
            (if s[0] == 'a' then 1 else 0) + CountAs(s[1..i]) + CountAs(s[i..]);
            == CountAs([s[0]]) + CountAs(s[1..i]) + CountAs(s[i..]);
            { 
                assert s[..1] == [s[0]];
                CountAsAdditivity(s[..i+1], 1);
            }
            CountAs(s[..i+1]) + CountAs(s[i..]);
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
    assert RemoveAs(s) == RemoveAs(t[..sLength]);
    {
        RemoveAsPrefix(t, sLength);
    }
    assert RemoveAs(t[..sLength]) == RemoveAs(s);
    if RemoveAs(s) != t[sLength..] {
        return ":(";
    }
    return s;
}
// </vc-code>

