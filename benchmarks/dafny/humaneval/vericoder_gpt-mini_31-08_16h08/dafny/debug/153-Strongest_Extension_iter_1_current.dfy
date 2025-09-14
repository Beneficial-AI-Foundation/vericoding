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
// No helper functions required for this proof.
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
  var best := extensions[0];
  var bestStrength := Extension.CalculateStrength(best);
  var i := 1;
  while i < |extensions|
    invariant 0 <= i <= |extensions|
    invariant 0 <= bestIndex < |extensions|
    invariant extensions[bestIndex] == best
    invariant forall j :: 0 <= j < i ==> Extension.CalculateStrength(best) >= Extension.CalculateStrength(extensions[j])
    decreases |extensions| - i
  {
    var cur := extensions[i];
    var curS := Extension.CalculateStrength(cur);
    if curS > bestStrength {
      bestIndex := i;
      best := cur;
      bestStrength := curS;
    }
    i := i + 1;
  }
  result := className + "." + best;
  assert result[..|className|] == className;
  assert result[|className|] == '.';
  assert result[|className| + 1..] == best;
}
// </vc-code>

