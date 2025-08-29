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
// Helper function to find the index of the strongest extension
method FindStrongestExtensionIndex(exts: seq<string>) returns (idx: int)
  ensures 0 <= idx < |exts| || |exts| == 0
  ensures forall i :: 0 <= i < |exts| ==> Extension.CalculateStrength(exts[idx]) >= Extension.CalculateStrength(exts[i])
  ensures forall i :: 0 <= i < idx ==> Extension.CalculateStrength(exts[idx]) > Extension.CalculateStrength(exts[i])
{
  if |exts| == 0 {
    return 0;
  }
  idx := 0;
  var maxStrength := Extension.CalculateStrength(exts[0]);
  for i := 1 to |exts|
    invariant 0 <= idx < |exts|
    invariant forall k :: 0 <= k < i ==> maxStrength >= Extension.CalculateStrength(exts[k])
    invariant maxStrength == Extension.CalculateStrength(exts[idx])
    invariant forall k :: 0 <= k < idx ==> Extension.CalculateStrength(exts[idx]) > Extension.CalculateStrength(exts[k])
  {
    var currentStrength := Extension.CalculateStrength(exts[i]);
    if currentStrength > maxStrength {
      idx := i;
      maxStrength := currentStrength;
    }
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def Strongest_Extension(class_name: String, extensions: List[String]) -> String
You will be given the name of a class (a string) and a list of extensions. The extensions are to be used to load additional classes to the class. The strength of the extension is as follows: Let CAP be the number of the uppercase letters in the extension's name, and let SM be the number of lowercase letters in the extension's name, the strength is given by the fraction CAP - SM. You should find the strongest extension and return a string in this format: ClassName.StrongestExtensionName. If there are two or more extensions with the same strength, you should choose the one that comes first in the list. For example, if you are given "Slices" as the class and a list of the extensions: ['SErviNGSliCes', 'Cheese', 'StuFfed'] then you should return 'Slices.SErviNGSliCes' since 'SErviNGSliCes' is the strongest extension (its strength is -1).
*/
// </vc-description>

// <vc-spec>
method StrongestExtension(className: string, extensions: seq<string>) returns (result: string)
  requires |extensions| > 0
  ensures exists i :: 0 <= i < |extensions| && result == className + "." + extensions[i]
  ensures forall i :: 0 <= i < |extensions| ==> Extension.CalculateStrength(extensions[i]) <= Extension.CalculateStrength(result[|className| + 1..])
  ensures forall i :: 0 <= i < |extensions| && Extension.CalculateStrength(extensions[i]) == Extension.CalculateStrength(result[|className| + 1..]) ==> i >= extensions[..].IndexOf(result[|className| + 1..])
// </vc-spec>
// <vc-code>
{
  var strongestIdx := FindStrongestExtensionIndex(extensions);
  result := className + "." + extensions[strongestIdx];
}
// </vc-code>
