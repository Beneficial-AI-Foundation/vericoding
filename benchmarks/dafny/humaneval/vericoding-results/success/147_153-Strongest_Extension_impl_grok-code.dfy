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
  /* code modified by LLM (iteration 5): Implemented linear search to find the extension with maximum strength, updating on strictly greater and keeping first on ties. */
  var max_str := Extension.CalculateStrength(extensions[0]);
  var chosen := extensions[0];
  var i := 1;
  while i < |extensions|
    invariant 0 <= i <= |extensions|
    invariant max_str == Extension.CalculateStrength(chosen)
    invariant chosen in extensions[0..i]
    invariant forall k :: 0 <= k < i ==> Extension.CalculateStrength(chosen) >= Extension.CalculateStrength(extensions[k])
  {
    var current_str := Extension.CalculateStrength(extensions[i]);
    if current_str > max_str {
      max_str := current_str;
      chosen := extensions[i];
    }
    i := i + 1;
  }
  result := className + "." + chosen;
}
// </vc-code>
