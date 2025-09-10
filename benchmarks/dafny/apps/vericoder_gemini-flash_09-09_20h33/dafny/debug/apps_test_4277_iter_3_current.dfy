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
function SplitString(s: string, separator: char): seq<string>
{
  if s == "" then []
  else if s.Contains(separator) then
    var i := s.IndexOf(separator);
    [s[..i]] + SplitString(s[i+1..], separator)
  else
    [s]
}

function IsValidInteger(s: string): bool
{
  if s == "" then false
  else
    (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

function StringToInt(s: string): int
  requires IsValidInteger(s)
  ensures StringToInt(s) >= 0
{
  if s == "" then 0 // Should not happen due to precondition
  else
    (s[0] as int - '0' as int) + (if |s| > 1 then 10 * StringToInt(s[1..]) else 0) // Fixed: changed multiplication order for correct integer conversion
}

function IntToString(n: int): string
  requires n >= 0
{
  if n == 0 then "0"
  else if n < 10 then "" + ('0' + n as char) // Fixed: correct character arithmetic
  else IntToString(n / 10) + ("" + ('0' + (n % 10) as char)) // Fixed: correct character arithmetic
}
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
      var n_str := parts[0];
      var a_str := parts[1];
      var b_str := parts[2];

      var n := StringToInt(n_str);
      var a := StringToInt(a_str);
      var b := StringToInt(b_str);

      if ValidInput(n, a, b) {
        result := IntToString(MinimumCost(n, a, b)) + "\n";
      } else {
        result := "";
      }
    } else {
      result := "";
    }
  } else {
    result := "";
  }
}
// </vc-code>

