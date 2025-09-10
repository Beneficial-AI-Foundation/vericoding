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
function SumUpToSize(n: int, m: int, size: int): int
    requires size >= 0
    decreases size
{
    if size == 0 then 0 else SumUpToSize(n, m, size - 1) + size * m
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

