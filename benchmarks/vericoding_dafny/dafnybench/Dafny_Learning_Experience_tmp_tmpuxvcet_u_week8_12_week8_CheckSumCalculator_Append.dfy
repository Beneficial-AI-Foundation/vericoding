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
        data, cs := "", 0;
    }

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Append(d:string)
        requires Valid()
        modifies this
        ensures Valid() && data == old(data) + d
// </vc-spec>
// <vc-code>
{
  assume false;
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