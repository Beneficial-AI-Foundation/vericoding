// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Replaced `ensures result in exts` with an equivalent `exists` quantifier to fix a compilation error. */
function FindStrongest(exts: seq<string>): (result: string)
    requires |exts| > 0
    ensures exists i :: 0 <= i < |exts| && result == exts[i]
    ensures forall i :: 0 <= i < |exts| ==> Extension.CalculateStrength(result) >= Extension.CalculateStrength(exts[i])
{
    if |exts| == 1 then
        exts[0]
    else
    {
        var strongest_in_tail := FindStrongest(exts[1..]);
        if Extension.CalculateStrength(exts[0]) >= Extension.CalculateStrength(strongest_in_tail) then
            exts[0]
        else
            strongest_in_tail
    }
}
// </vc-helpers>

// <vc-spec>
method Strongest_Extension(className: string, extensions: seq<string>) returns (result: string)

    requires |extensions| > 0

    ensures |result| > |className|
    ensures result[..|className|] == className
    ensures result[|className|] == '.'
    ensures var extName := result[|className| + 1..];
               extName in extensions
    ensures var extName := result[|className| + 1..];
               forall i :: 0 <= i < |extensions| ==> Extension.CalculateStrength(extName) >= Extension.CalculateStrength(extensions[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The code is correct as the fix was in the helper function it depends on. */
{
  var strongestExt := FindStrongest(extensions);
  result := className + "." + strongestExt;
}
// </vc-code>
