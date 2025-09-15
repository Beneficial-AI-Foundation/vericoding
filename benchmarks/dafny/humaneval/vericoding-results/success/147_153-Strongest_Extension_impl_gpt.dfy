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
lemma LemmaConcatDotProps(c: string, e: string)
  ensures |c + "." + e| > |c|
  ensures (c + "." + e)[..|c|] == c
  ensures (c + "." + e)[|c|] == '.'
  ensures (c + "." + e)[|c| + 1..] == e
{}

lemma SeqIndexIsMember<T>(s: seq<T>, i: int)
  requires 0 <= i < |s|
  ensures s[i] in s
{}
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
  var n := |extensions|;
  var bestIdx: nat := 0;
  var bestStrength := Extension.CalculateStrength(extensions[0]);
  var i: nat := 1;
  while i < n
    invariant 0 < n
    invariant 0 <= bestIdx < i
    invariant i <= n
    invariant bestStrength == Extension.CalculateStrength(extensions[bestIdx])
    invariant forall j :: 0 <= j < i ==> bestStrength >= Extension.CalculateStrength(extensions[j])
    decreases n - i
  {
    var s := Extension.CalculateStrength(extensions[i]);
    if s > bestStrength {
      bestIdx := i;
      bestStrength := s;
    }
    i := i + 1;
  }
  var ext := extensions[bestIdx];
  result := className + "." + ext;
  LemmaConcatDotProps(className, ext);
  SeqIndexIsMember(extensions, bestIdx);
  assert result[..|className|] == className;
  assert result[|className|] == '.';
  assert result[|className| + 1..] == ext;
  assert forall j :: 0 <= j < n ==> Extension.CalculateStrength(ext) >= Extension.CalculateStrength(extensions[j]);
}
// </vc-code>
