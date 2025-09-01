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
        var m :| 0 <= m < |sub| && forall i :: 0 <= i < |sub| ==> 
            Extension.CalculateStrength(sub[m]) >= Extension.CalculateStrength(sub[i]);
        if Extension.CalculateStrength(extensions[0]) >= Extension.CalculateStrength(sub[m]) {
            // first element is the maximum
        } else {
            // m+1 is the maximum since m is index in sub which is extensions[1..]
        }
    }
}

lemma StrengthConsistent(extName: string, extensions: seq<string>)
    requires extName in extensions
    ensures Extension.CalculateStrength(extName) <= Extension.CalculateStrength(extName)
{
    // trivial
}

lemma LoopInvariantMaintained(extensions: seq<string>, index: int, bestIndex: int, bestStrength: int)
    requires 0 <= bestIndex < index <= |extensions|
    requires bestStrength == Extension.CalculateStrength(extensions[bestIndex])
    requires forall i :: 0 <= i < index ==> bestStrength >= Extension.CalculateStrength(extensions[i])
    requires index < |extensions|
    ensures forall i :: 0 <= i < index + 1 ==> 
        max(bestStrength, Extension.CalculateStrength(extensions[index])) >= Extension.CalculateStrength(extensions[i])
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
    var bestIndex := 0;
    var bestStrength := Extension.CalculateStrength(extensions[0]);
    var index := 1;
    
    while index < |extensions|
        invariant 0 <= bestIndex < index <= |extensions|
        invariant bestStrength == Extension.CalculateStrength(extensions[bestIndex])
        invariant forall i :: 0 <= i < index ==> bestStrength >= Extension.CalculateStrength(extensions[i])
    {
        var currentStrength := Extension.CalculateStrength(extensions[index]);
        if currentStrength > bestStrength {
            bestIndex := index;
            bestStrength := currentStrength;
        } else {
            // bestStrength remains the maximum
        }
        index := index + 1;
    }
    
    result := className + "." + extensions[bestIndex];
}
// </vc-code>

