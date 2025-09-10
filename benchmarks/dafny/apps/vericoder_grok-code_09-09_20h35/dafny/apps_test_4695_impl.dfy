predicate ValidInput(input: string)
    requires |input| > 0
{
    var parts := SplitStringPure(input);
    |parts| >= 2 && IsValidInt(parts[0]) && IsValidInt(parts[1])
}

predicate SameGroup(a: int, b: int)
{
    var n1 := [1, 3, 5, 7, 8, 10, 12];
    var n2 := [4, 6, 9, 11];
    (a in n1 && b in n1) || (a in n2 && b in n2) || (a == 2 && b == 2)
}

predicate CorrectOutput(input: string, result: string)
    requires |input| > 0
{
    if ValidInput(input) then
        var parts := SplitStringPure(input);
        var a := StringToIntPure(parts[0]);
        var b := StringToIntPure(parts[1]);
        (result == "Yes\n" <==> SameGroup(a, b)) && (result == "No\n" <==> !SameGroup(a, b))
    else
        result == ""
}

// <vc-helpers>
function SplitStringPure(s: string): seq<string> 
  requires s != ""
{
  s.Split(x => x == ' ')
}

function CharToInt(c: char): int {
  c as int - '0' as int
}

function StringToIntPure(s: string): int 
  requires IsValidInt(s)
  decreases |s|
{
  if |s| == 1 then CharToInt(s[0]) else CharToInt(s[0]) + 10 * StringToIntPure(s[1..])
}

predicate IsValidInt(s: string) {
  |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9' && (|s| == 1 || s[0] != '0')
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures result == "Yes\n" || result == "No\n" || result == ""
    ensures CorrectOutput(input, result)
// </vc-spec>
// <vc-code>
{
  if !ValidInput(input) {
    result := "";
  } else {
    var parts := SplitStringPure(input);
    var a := StringToIntPure(parts[0]);
    var b := StringToIntPure(parts[1]);
    if SameGroup(a, b) {
      result := "Yes\n";
    } else {
      result := "No\n";
    }
  }
}
// </vc-code>

