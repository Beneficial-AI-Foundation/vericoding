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
function GetStrongestExtension(extensions: seq<string>): string
    requires |extensions| > 0
    ensures exists i :: 0 <= i < |extensions| && GetStrongestExtension(extensions) == extensions[i]
    ensures forall i :: 0 <= i < |extensions| ==> Extension.CalculateStrength(GetStrongestExtension(extensions)) >= Extension.CalculateStrength(extensions[i])
{
    if |extensions| == 1 then
        extensions[0]
    else
        var s1 := GetStrongestExtension(extensions[..|extensions|-1]);
        var s2 := extensions[|extensions|-1];
        if Extension.CalculateStrength(s1) >= Extension.CalculateStrength(s2) then
            s1
        else
            s2
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
    var strongestExt := GetStrongestExtension(extensions);
    return className + "." + strongestExt;
}
// </vc-code>

