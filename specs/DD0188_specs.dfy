// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Append(d:string)
        requires Valid()
        modifies this
        ensures Valid() && data == old(data) + d
// </vc-spec>
// <vc-code>
{
        var i := 0;
        while i != |d| 
            invariant 0<= i <= |d|
            invariant Valid()
            invariant data == old(data) + d[..i]
        {
            cs := (cs + d[i] as int) % 137;
            data := data + [d[i]];
            i := i +1;
        }
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