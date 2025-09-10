predicate ValidInput(input: string)
{
    |input| > 0 && 
    (var nm := ParseTwoInts(input);
     var n := nm.0; var m := nm.1;
     n > 0 && m > 0)
}

function ParseTwoInts(input: string): (int, int)
    requires |input| > 0
{
    var lines := SplitLinesFunc(input);
    if |lines| == 0 then (0, 0)
    else 
        var parts := SplitSpacesFunc(lines[0]);
        if |parts| < 2 then (0, 0)
        else (StringToInt(parts[0]), StringToInt(parts[1]))
}

function ComputeHappinessSum(n: int, m: int): int
    requires n > 0 && m > 0
{
    SumUpToSize(n, m, n)
}

// <vc-helpers>
// To fix unresolved identifiers and type selection errors by defining helper functions
function SplitLinesFunc(input: string): seq<string>
  decreases |input|
{
  if |input| == 0 then []
  else
    var pos := 0;
    while pos < |input| && input[pos] != '\n' 
      invariant 0 <= pos <= |input|
    {
      pos := pos + 1;
    }
    if pos >= |input| then [input]
    else [input[0..pos]] + SplitLinesFunc(input[(pos + 1)..])
}

function SplitSpacesFunc(s: string): seq<string>
  decreases |s|
{
  if |s| == 0 then []
  else
    var pos := 0;
    while pos < |s| && s[pos] == ' ' 
      invariant 0 <= pos <= |s|
    {
      pos := pos + 1;
    }
    if pos >= |s| then []
    else
      var end := pos;
      while end < |s| && s[end] != ' ' 
        invariant pos <= end <= |s|
      {
        end := end + 1;
      }
      [s[pos..end]] + SplitSpacesFunc(s[end..])
}

function StringToInt(s: string): int
  requires forall i | 0 <= i < |s| :: '0' <= s[i] <= '9'
  decreases |s|
{
  if |s| == 0 then 0
  else StringToInt(s[..(|s|-1)]) * 10 + (s[|s|-1] - '0')
}

function IntToString(i: int): string
  requires i >= 0
  decreases i
{
  if i == 0 then "0"
  else IntToString(i / 10) + [('0' + (i % 10))]
}

function SumUpToSize(n: int, m: int, k: int): int
  requires n > 0 && m > 0 && k >= 0
  decreases k
{
  if k == 0 then 0
  else m * k + SumUpToSize(n, m, k-1)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    ensures |output| >= 0
    ensures ValidInput(input) ==> 
        (var nm := ParseTwoInts(input);
         var n := nm.0; var m := nm.1;
         output == IntToString(ComputeHappinessSum(n, m)) + "\n")
    ensures ValidInput(input) ==> |output| > 0 && output[|output|-1] == '\n'
    ensures ValidInput(input) ==> forall c :: c in output ==> (c == '\n' || ('0' <= c <= '9'))
    ensures !ValidInput(input) ==> output == ""
// </vc-spec>
// <vc-code>
{
  var nm := ParseTwoInts(input);
  var n := nm.0;
  var m := nm.1;
  if n > 0 && m > 0 {
    var sum := ComputeHappinessSum(n, m);
    output := IntToString(sum) + "\n";
  } else {
    output := "";
  }
}
// </vc-code>

