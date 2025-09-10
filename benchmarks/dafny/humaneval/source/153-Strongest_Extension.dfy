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
// pure-end
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
{
    // impl-start
    var strongestExt := new Extension(extensions[0]);
    ghost var strongestIndex := 0;

    for i := 1 to |extensions|
        // invariants-start
        invariant 0 <= strongestIndex < |extensions|
        invariant strongestExt.name == extensions[strongestIndex]
        invariant strongestExt.strength == Extension.CalculateStrength(extensions[strongestIndex])
        invariant forall j :: 0 <= j < i ==> strongestExt.strength >= Extension.CalculateStrength(extensions[j])
        invariant forall j :: 0 <= j < i ==> Extension.CalculateStrength(extensions[strongestIndex]) >= Extension.CalculateStrength(extensions[j])
        // invariants-end
    {
        var currentExt := new Extension(extensions[i]);
        if currentExt.strength > strongestExt.strength {
            strongestExt := currentExt;
            strongestIndex := i;
        }
    }

    result := className + "." + strongestExt.name;
    // impl-end
}
