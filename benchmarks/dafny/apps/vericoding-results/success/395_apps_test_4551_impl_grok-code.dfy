predicate ValidParseable(input: string)
{
    var parts := SplitStringPure(input);
    |parts| >= 4
}

predicate AllPartsAreIntegers(input: string)
{
    var parts := SplitStringPure(input);
    |parts| >= 4 &&
    IsValidInteger(parts[0]) &&
    IsValidInteger(parts[1]) &&
    IsValidInteger(parts[2]) &&
    IsValidInteger(parts[3])
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> ('0' <= s[i] <= '9') || (i == 0 && s[i] == '-'))
}

predicate ValidParse(input: string, a: int, b: int, c: int, d: int)
{
    var parts := SplitStringPure(input);
    |parts| >= 4 && 
    IsValidInteger(parts[0]) &&
    IsValidInteger(parts[1]) &&
    IsValidInteger(parts[2]) &&
    IsValidInteger(parts[3]) &&
    StringToIntPure(parts[0]) == a &&
    StringToIntPure(parts[1]) == b &&
    StringToIntPure(parts[2]) == c &&
    StringToIntPure(parts[3]) == d
}

function SplitStringPure(s: string): seq<string>
{
    SplitStringHelper(s, 0, "", [])
}

function SplitStringHelper(s: string, i: int, current: string, acc: seq<string>): seq<string>
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i == |s| then
        if |current| > 0 then acc + [current] else acc
    else if s[i] == ' ' || s[i] == '\n' || s[i] == '\t' then
        if |current| > 0 then
            SplitStringHelper(s, i + 1, "", acc + [current])
        else
            SplitStringHelper(s, i + 1, "", acc)
    else
        SplitStringHelper(s, i + 1, current + [s[i]], acc)
}

function StringToIntPure(s: string): int
    requires IsValidInteger(s)
{
    if |s| > 0 && s[0] == '-' then
        -StringToIntHelperUnsigned(s, 1, 0)
    else
        StringToIntHelperUnsigned(s, 0, 0)
}

function StringToIntHelperUnsigned(s: string, i: int, acc: int): int
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i == |s| then acc
    else if '0' <= s[i] <= '9' then
        StringToIntHelperUnsigned(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
    else
        acc
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    ensures (forall a, b, c, d: int :: 
        ValidParse(input, a, b, c, d) ==> 
        (result == "Left\n" <==> a + b > c + d) &&
        (result == "Right\n" <==> a + b < c + d) &&
        (result == "Balanced\n" <==> a + b == c + d))
    ensures ValidParseable(input) && AllPartsAreIntegers(input) ==> (result == "Left\n" || result == "Right\n" || result == "Balanced\n")
    ensures (!ValidParseable(input) || !AllPartsAreIntegers(input)) ==> result == ""
// </vc-spec>
// <vc-code>
{
  var parts := SplitStringPure(input);
  if |parts| < 4 {
    return "";
  }
  var s1 := parts[0];
  var s2 := parts[1];
  var s3 := parts[2];
  var s4 := parts[3];
  if !IsValidInteger(s1) || !IsValidInteger(s2) || !IsValidInteger(s3) || !IsValidInteger(s4) {
    return "";
  }
  var a := StringToIntPure(s1);
  var b := StringToIntPure(s2);
  var c := StringToIntPure(s3);
  var d := StringToIntPure(s4);
  var left := a + b;
  var right := c + d;
  if left > right {
    return "Left\n";
  } else if left < right {
    return "Right\n";
  } else {
    return "Balanced\n";
  }
}
// </vc-code>

