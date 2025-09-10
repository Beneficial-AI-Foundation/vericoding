predicate ValidInput(S: string)
{
    |S| >= 3 && forall i :: 0 <= i < |S| ==> '1' <= S[i] <= '9'
}

function StringToInt(s: string): int
    requires |s| == 3
    requires forall i :: 0 <= i < |s| ==> '1' <= s[i] <= '9'
    ensures StringToInt(s) >= 111
    ensures StringToInt(s) <= 999
{
    100 * ((s[0] as int) - ('0' as int)) + 
    10 * ((s[1] as int) - ('0' as int)) + 
    ((s[2] as int) - ('0' as int))
}

function abs(x: int): int
    ensures abs(x) >= 0
    ensures abs(x) == x || abs(x) == -x
{
    if x >= 0 then x else -x
}

predicate IsMinimumDifference(S: string, result: int)
    requires ValidInput(S)
{
    result >= 0 &&
    (exists i :: 0 <= i <= |S| - 3 && result == abs(753 - StringToInt(S[i..i+3]))) &&
    (forall i :: 0 <= i <= |S| - 3 ==> result <= abs(753 - StringToInt(S[i..i+3])))
}

// <vc-helpers>
predicate IsMinimumDifference(S: string, result: int)
    requires ValidInput(S)
{
    result >= 0 &&
    (exists i :: 0 <= i <= |S| - 3 && {:trigger abs(753 - StringToInt(S[i..i+3]))} result == abs(753 - StringToInt(S[i..i+3]))) &&
    (forall i :: 0 <= i <= |S| - 3 ==> {:trigger abs(753 - StringToInt(S[i..i+3]))} result <= abs(753 - StringToInt(S[i..i+3])))
}
// </vc-helpers>

// <vc-spec>
method solve(S: string) returns (result: int)
    requires ValidInput(S)
    ensures IsMinimumDifference(S, result)
// </vc-spec>
// <vc-code>
var min := 643;
  var i := 0;
  while i <= |S| - 3
    invariant 0 <= i <= |S| - 3 + 1
    invariant min >= 0
    invariant min <= 643
    invariant forall j :: 0 <= j < i ==> {:trigger abs(753 - StringToInt(S[j..j+3]))} min <= abs(753 - StringToInt(S[j..j+3]))
    invariant if i > 0 then exists k :: 0 <= k < i && min == abs(753 - StringToInt(S[k..k+3]))
  {
    var sub := S[i..i+3];
    var val := StringToInt(sub);
    var diff := abs(753 - val);
    if diff < min {
      min := diff;
    }
    i := i + 1;
  }
  result := min;
// </vc-code>

