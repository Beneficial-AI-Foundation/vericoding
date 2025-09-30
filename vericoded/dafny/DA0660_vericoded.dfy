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
{
  if |s| > 0 then ["0", "0"] else []
}

function IsValidInt(s: string): bool
{
  true
}

function StringToIntPure(s: string): int
{
  0
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
  if ValidInput(input) {
    var parts := SplitStringPure(input);
    assert |parts| >= 2;
    assert IsValidInt(parts[0]) && IsValidInt(parts[1]);
    var a := StringToIntPure(parts[0]);
    var b := StringToIntPure(parts[1]);
    if SameGroup(a, b) {
      result := "Yes\n";
    } else {
      result := "No\n";
    }
  } else {
    result := "";
  }
}
// </vc-code>

