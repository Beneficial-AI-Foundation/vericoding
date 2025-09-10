predicate ValidInput(n: int, a: int, b: int)
{
    1 <= n <= 20 && 1 <= a <= 50 && 1 <= b <= 50
}

function TrainCost(n: int, a: int): int
{
    n * a
}

function MinimumCost(n: int, a: int, b: int): int
{
    var trainCost := TrainCost(n, a);
    if trainCost < b then trainCost else b
}

predicate CorrectResult(input: string, result: string)
{
    var lines := SplitString(input, '\n');
    if |lines| > 0 then
        var parts := SplitString(lines[0], ' ');
        if |parts| >= 3 && IsValidInteger(parts[0]) && IsValidInteger(parts[1]) && IsValidInteger(parts[2]) then
            var n := StringToInt(parts[0]);
            var a := StringToInt(parts[1]);
            var b := StringToInt(parts[2]);
            ValidInput(n, a, b) ==> result == IntToString(MinimumCost(n, a, b)) + "\n"
        else
            result == ""
    else
        result == ""
}

// <vc-helpers>
// No additional helper code required.
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures CorrectResult(input, result)
// </vc-spec>
// <vc-code>
{
  var lines := SplitString(input, '\n');
  if |lines| > 0 {
    var parts := SplitString(lines[0], ' ');
    if |parts| >= 3 && IsValidInteger(parts[0]) && IsValidInteger(parts[1]) && IsValidInteger(parts[2]) {
      var n := StringToInt(parts[0]);
      var a := StringToInt(parts[1]);
      var b := StringToInt(parts[2]);
      if ValidInput(n, a, b) {
        result := IntToString(MinimumCost(n, a, b)) + "\n";
        return;
      } else {
        result := "";
        return;
      }
    } else {
      result := "";
      return;
    }
  } else {
    result := "";
    return;
  }
}
// </vc-code>

