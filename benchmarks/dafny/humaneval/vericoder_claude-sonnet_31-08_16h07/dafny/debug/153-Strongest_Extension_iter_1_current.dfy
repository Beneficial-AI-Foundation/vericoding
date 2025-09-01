class Extension {
    var name: string
    var strength: int
    constructor(n: string)
        ensures name == n
        ensures strength == CalculateStrength(n)
    {
        name := n;
        strength := CalculateStrength(n);
    }
    static function CalculateStrength(s: string): int
    {
        CountUpperCase(s) - CountLowerCase(s)
    }
    static function CountUpperCase(s: string): int
    {
        if |s| == 0 then 0
        else (if 'A' <= s[0] <= 'Z' then 1 else 0) + CountUpperCase(s[1..])
    }
    static function CountLowerCase(s: string): int
    {
        if |s| == 0 then 0
        else (if 'a' <= s[0] <= 'z' then 1 else 0) + CountLowerCase(s[1..])
    }
}

// <vc-helpers>
lemma MaxStrengthExists(extensions: seq<string>)
    requires |extensions| > 0
    ensures exists i :: 0 <= i < |extensions| && 
            forall j :: 0 <= j < |extensions| ==> Extension.CalculateStrength(extensions[i]) >= Extension.CalculateStrength(extensions[j])
{
    var maxIdx := FindMaxStrengthIndex(extensions, 0, 0);
    assert 0 <= maxIdx < |extensions|;
    assert forall j :: 0 <= j < |extensions| ==> Extension.CalculateStrength(extensions[maxIdx]) >= Extension.CalculateStrength(extensions[j]);
}

function FindMaxStrengthIndex(extensions: seq<string>, currentIdx: int, maxIdx: int): int
    requires |extensions| > 0
    requires 0 <= currentIdx <= |extensions|
    requires 0 <= maxIdx < |extensions|
    requires forall i :: 0 <= i < currentIdx ==> Extension.CalculateStrength(extensions[maxIdx]) >= Extension.CalculateStrength(extensions[i])
    ensures 0 <= FindMaxStrengthIndex(extensions, currentIdx, maxIdx) < |extensions|
    ensures forall i :: 0 <= i < |extensions| ==> Extension.CalculateStrength(extensions[FindMaxStrengthIndex(extensions, currentIdx, maxIdx)]) >= Extension.CalculateStrength(extensions[i])
    decreases |extensions| - currentIdx
{
    if currentIdx == |extensions| then maxIdx
    else if Extension.CalculateStrength(extensions[currentIdx]) > Extension.CalculateStrength(extensions[maxIdx]) then
        FindMaxStrengthIndex(extensions, currentIdx + 1, currentIdx)
    else
        FindMaxStrengthIndex(extensions, currentIdx + 1, maxIdx)
}
// </vc-helpers>

// <vc-spec>
method Strongest_Extension(className: string, extensions: seq<string>) returns (result: string)
    // pre-conditions-start
    requires |extensions| > 0
    // pre-conditions-end
    // post-conditions-start
    ensures |result| > |className|
    ensures result[..|className|] == className
    ensures result[|className|] == '.'
    ensures var extName := result[|className| + 1..];
               extName in extensions
    ensures var extName := result[|className| + 1..];
               forall i :: 0 <= i < |extensions| ==> Extension.CalculateStrength(extName) >= Extension.CalculateStrength(extensions[i])
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var maxIdx := FindMaxStrengthIndex(extensions, 0, 0);
    result := className + "." + extensions[maxIdx];
}
// </vc-code>

