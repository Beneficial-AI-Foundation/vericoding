function sum(s: seq<int>, i: nat): int
    requires i <= |s|
{
    if i == 0 then 0 else sum(s, i-1) + s[i-1]
}

ghost function Hash(s:string):int {
    SumChars(s) % 137
}

ghost function SumChars(s: string):int {
    if |s| == 0 then 0 else 
        s[|s| - 1] as int + SumChars(s[..|s| -1])
}
class CheckSumCalculator{
    var data: string
    var cs:int

    ghost predicate Valid()
        reads this
    {
        cs == Hash(data)
    }

    constructor ()
        ensures Valid() && data == ""
    {
        data, cs := "", 0;"
    }

// <vc-helpers>
lemma SumCharsConcat(s1: string, s2: string)
    ensures SumChars(s1 + s2) == SumChars(s1) + SumChars(s2)
{
    if |s2| == 0 {
        assert s1 + s2 == s1;
    } else {
        calc {
            SumChars(s1 + s2);
            == (s1 + s2)[|s1 + s2| - 1] as int + SumChars((s1 + s2)[..|s1 + s2| - 1]);
            == (s1 + s2)[|s1| + |s2| - 1] as int + SumChars((s1 + s2)[..|s1| + |s2| - 1]);
            == s2[|s2| - 1] as int + SumChars(s1 + s2[..|s2| - 1]);
        }
        SumCharsConcat(s1, s2[..|s2| - 1]);
        calc {
            SumChars(s1 + s2);
            == s2[|s2| - 1] as int + SumChars(s1 + s2[..|s2| - 1]);
            == s2[|s2| - 1] as int + SumChars(s1) + SumChars(s2[..|s2| - 1]);
            == SumChars(s1) + (s2[|s2| - 1] as int + SumChars(s2[..|s2| - 1]));
            == SumChars(s1) + SumChars(s2);
        }
    }
}

lemma HashConcat(s1: string, s2: string)
    ensures Hash(s1 + s2) == (Hash(s1) + SumChars(s2)) % 137
{
    SumCharsConcat(s1, s2);
    calc {
        Hash(s1 + s2);
        == SumChars(s1 + s2) % 137;
        == (SumChars(s1) + SumChars(s2)) % 137;
        == (SumChars(s1) % 137 + SumChars(s2)) % 137;
        == (Hash(s1) + SumChars(s2)) % 137;
    }
}
// </vc-helpers>

// <vc-spec>
method Append(d:string)
        requires Valid()
        modifies this
        ensures Valid() && data == old(data) + d
// </vc-spec>
// <vc-code>
{
    HashConcat(data, d);
    data := data + d;
    cs := (cs + SumChars(d)) % 137;
}
// </vc-code>

function GetData(): string
        requires Valid()
        reads this
        ensures Hash(GetData()) == Checksum()
    {
        data
    }

    function Checksum(): int 
        requires Valid()
        reads this 
        ensures Checksum() == Hash(data)
    {
        cs
    }
}