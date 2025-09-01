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
// No additional helpers needed for this implementation.
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
    var maxStrength: int := Extension.CalculateStrength(extensions[0]);
    var strongestExt: string := extensions[0];
    
    var i: int := 1;
    while i < |extensions|
        invariant 0 <= i <= |extensions|
        invariant strongestExt in extensions[..i]
        invariant forall k :: 0 <= k < i ==> Extension.CalculateStrength(strongestExt) >= Extension.CalculateStrength(extensions[k])
    {
        var currentStrength: int := Extension.CalculateStrength(extensions[i]);
        if currentStrength >= maxStrength {
            maxStrength := currentStrength;
            strongestExt := extensions[i];
        }
        i := i + 1;
    }
    
    result := className + "." + strongestExt;
}
// </vc-code>

