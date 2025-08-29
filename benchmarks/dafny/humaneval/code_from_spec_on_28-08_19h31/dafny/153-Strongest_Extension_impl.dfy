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
lemma MaxStrengthLemma(extensions: seq<string>, maxExt: string, maxStrength: int)
    requires |extensions| > 0
    requires maxExt in extensions
    requires maxStrength == Extension.CalculateStrength(maxExt)
    requires forall i :: 0 <= i < |extensions| ==> maxStrength >= Extension.CalculateStrength(extensions[i])
    ensures forall i :: 0 <= i < |extensions| ==> Extension.CalculateStrength(maxExt) >= Extension.CalculateStrength(extensions[i])
{
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
    var maxStrength := Extension.CalculateStrength(extensions[0]);
    var maxExt := extensions[0];
    var i := 1;
    
    while i < |extensions|
        invariant 0 <= i <= |extensions|
        invariant maxExt in extensions
        invariant maxStrength == Extension.CalculateStrength(maxExt)
        invariant forall k :: 0 <= k < i ==> maxStrength >= Extension.CalculateStrength(extensions[k])
    {
        var currStrength := Extension.CalculateStrength(extensions[i]);
        if currStrength > maxStrength {
            maxStrength := currStrength;
            maxExt := extensions[i];
        }
        i := i + 1;
    }
    
    result := className + "." + maxExt;
    assert |result| > |className|;
    assert result[..|className|] == className;
    assert result[|className|] == '.';
    assert result[|className| + 1..] == maxExt;
    assert maxExt in extensions;
    MaxStrengthLemma(extensions, maxExt, maxStrength);
}
// </vc-code>
