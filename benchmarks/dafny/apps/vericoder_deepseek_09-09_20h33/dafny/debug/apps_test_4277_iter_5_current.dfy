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
function SplitString(s: string, sep: char): seq<string>
  requires |s| > 0
  ensures |SplitString(s, sep)| >= 1
  ensures forall i :: 0 <= i < |SplitString(s, sep)| ==> |SplitString(s, sep)[i]| >= 0
{
  var i := 0;
  var result: seq<string> := [];
  var current := "";
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| >= 0
    invariant |current| >= 0
  {
    if s[i] == sep {
      result := result + [current];
      current := "";
    } else {
      current := current + [s[i]];
    }
    i := i + 1;
  }
  result := result + [current];
  result
}

function IsValidInteger(s: string): bool
  ensures IsValidInteger(s) ==> |s| > 0
{
  |s| > 0 && 
  (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9') && 
  (|s| == 1 || s[0] != '0')
}

function StringToInt(s: string): int
  requires IsValidInteger(s)
{
  if |s| == 1 then
    s[0] as int - '0' as int
  else
    (s[0] as int - '0' as int) * pow(10, |s| - 1) + StringToInt(s[1..])
}

function pow(base: int, exponent: int): int
  requires exponent >= 0
  ensures exponent == 0 ==> pow(base, exponent) == 1
  ensures exponent > 0 ==> pow(base, exponent) == base * pow(base, exponent - 1)
{
  if exponent == 0 then 1 else base * pow(base, exponent - 1)
}

function IntToString(n: int): string
  requires n >= 0
  ensures |IntToString(n)| >= 1
{
  if n < 10 then 
    [(('0' as int) + n) as char] 
  else 
    IntToString(n / 10) + [(('0' as int) + (n % 10)) as char]
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
  if |lines| == 0 {
    result := "";
    return;
  }
  
  if |lines[0]| == 0 {
    result := "";
    return;
  }
  
  var parts := SplitString(lines[0], ' ');
  if |parts| < 3 {
    result := "";
    return;
  }
  
  if !IsValidInteger(parts[0]) || !IsValidInteger(parts[1]) || !IsValidInteger(parts[2]) {
    result := "";
    return;
  }
  
  var n := StringToInt(parts[0]);
  var a := StringToInt(parts[1]);
  var b := StringToInt(parts[2]);
  
  if !(1 <= n <= 20 && 1 <= a <= 50 && 1 <= b <= 50) {
    result := "";
    return;
  }
  
  var trainCost := n * a;
  if trainCost < b {
    result := IntToString(trainCost) + "\n";
  } else {
    result := IntToString(b) + "\n";
  }
}
// </vc-code>

