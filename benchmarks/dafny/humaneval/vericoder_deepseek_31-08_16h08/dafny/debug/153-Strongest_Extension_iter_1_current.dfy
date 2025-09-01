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
    ensures exists k :: 0 <= k < |extensions| && forall i :: 0 <= i < |extensions| ==> 
            Extension.CalculateStrength(extensions[k]) >= Extension.CalculateStrength(extensions[i])
{
    if |extensions| == 1 {
        // trivial case
    } else {
        var sub := extensions[1..];
        MaxStrengthExists(sub);
    }
}

lemma StrengthConsistent(extName: string, extensions: seq<string>)
    requires extName in extensions
    ensures Extension.CalculateStrength(extName) <= Extension.CalculateStrength(extName)
{
    // trivial
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
    var bestIndex := 0;
    var bestStrength := Extension.CalculateStrength(extensions[0]);
    var index := 1;
    
    while index < |extensions|
        invariant 1 <= index <= |extensions|
        invariant bestIndex >= 0 && bestIndex < index
        invariant bestStrength == Extension.CalculateStrength(extensions[bestIndex])
        invariant forall i :: 0 <= i < index ==> bestStrength >= Extension.CalculateStrength(extensions[i])
    {
        var currentStrength := Extension.CalculateStrength(extensions[index]);
        if currentStrength > bestStrength {
            bestIndex := index;
            bestStrength := currentStrength;
        }
        index := index + 1;
    }
    
    result := className + "." + extensions[bestIndex];
}
// </vc-code>

