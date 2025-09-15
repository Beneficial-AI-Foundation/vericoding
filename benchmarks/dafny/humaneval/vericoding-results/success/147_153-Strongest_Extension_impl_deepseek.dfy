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
function MaxExt(i: int, j: int, extensions: seq<string>): (maxIndex: int)
  requires 0 <= i <= j < |extensions|
  ensures i <= maxIndex <= j
  ensures forall k :: i <= k <= j ==> Extension.CalculateStrength(extensions[maxIndex]) >= Extension.CalculateStrength(extensions[k])
  decreases j - i
{
  if i == j then
    i
  else
    var mid := i + (j - i) / 2;
    var leftMax := MaxExt(i, mid, extensions);
    var rightMax := MaxExt(mid + 1, j, extensions);
    if Extension.CalculateStrength(extensions[leftMax]) >= Extension.CalculateStrength(extensions[rightMax]) then
      leftMax
    else
      rightMax
}

/* helper modified by LLM (iteration 2): Added decreases clause and strengthened postcondition */
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
  /* code modified by LLM (iteration 2): Use recursive helper function instead of loop */
  var maxIndex: int;
  maxIndex := MaxExt(0, |extensions| - 1, extensions);
  result := className + "." + extensions[maxIndex];
}
// </vc-code>
