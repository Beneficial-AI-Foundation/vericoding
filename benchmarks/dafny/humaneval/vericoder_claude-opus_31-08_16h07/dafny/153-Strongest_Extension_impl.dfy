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
lemma StrengthComparison(ext1: string, ext2: string)
    ensures Extension.CalculateStrength(ext1) >= Extension.CalculateStrength(ext2) || 
            Extension.CalculateStrength(ext2) >= Extension.CalculateStrength(ext1)
{
    // This lemma states that strength comparison is total
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
    var strongestIdx := 0;
    
    var i := 1;
    while i < |extensions|
        invariant 1 <= i <= |extensions|
        invariant 0 <= strongestIdx < |extensions|
        invariant maxStrength == Extension.CalculateStrength(extensions[strongestIdx])
        invariant forall j :: 0 <= j < i ==> maxStrength >= Extension.CalculateStrength(extensions[j])
    {
        var currentStrength := Extension.CalculateStrength(extensions[i]);
        if currentStrength > maxStrength {
            maxStrength := currentStrength;
            strongestIdx := i;
        }
        i := i + 1;
    }
    
    result := className + "." + extensions[strongestIdx];
}
// </vc-code>

