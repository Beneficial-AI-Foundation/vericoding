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
/* helper modified by LLM (iteration 2): added lemma to prove extension membership preservation */
lemma ExtensionMembershipLemma(extensions: seq<string>, bestExt: string, i: int, newExt: string)
  requires 0 <= i < |extensions|
  requires bestExt in extensions
  requires newExt == extensions[i]
  ensures newExt in extensions
{
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
{
  /* code modified by LLM (iteration 2): fixed loop invariant by updating maxStrength consistently */
  var maxStrength := Extension.CalculateStrength(extensions[0]);
  var bestExtension := extensions[0];
  
  for i := 1 to |extensions|
    invariant 0 <= i <= |extensions|
    invariant bestExtension in extensions
    invariant maxStrength == Extension.CalculateStrength(bestExtension)
    invariant forall j :: 0 <= j < i ==> Extension.CalculateStrength(bestExtension) >= Extension.CalculateStrength(extensions[j])
  {
    var currentStrength := Extension.CalculateStrength(extensions[i]);
    if currentStrength > maxStrength {
      maxStrength := currentStrength;
      bestExtension := extensions[i];
    }
  }
  
  result := className + "." + bestExtension;
}
// </vc-code>
