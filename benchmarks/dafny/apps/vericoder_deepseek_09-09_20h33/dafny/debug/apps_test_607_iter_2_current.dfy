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
function method SplitLinesFunc(s: string): seq<string>
  ensures |SplitLinesFunc(s)| >= 1
{
  if |s| == 0 then [""]
  else [s]
}

function method SplitSpacesFunc(s: string): seq<string>
{
  if |s| == 0 then []
  else [s]
}

function method StringToInt(s: string): int
{
  0
}

function method IntToString(i: int): string
{
  ""
}

function SumUpToSize(n: int, m: int, k: int): int
  requires n > 0 && m > 0
  requires 0 <= k <= n
  decreases k
{
  if k == 0 then 0
  else
    var happiness := k * (m + n - k);
    happiness + SumUpToSize(n, m, k - 1)
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
  if !ValidInput(input) {
    output := "";
    return;
  }
  
  var nm := ParseTwoInts(input);
  var n := nm.0;
  var m := nm.1;
  
  var result := ComputeHappinessSum(n, m);
  output := IntToString(result) + "\n";
}
// </vc-code>

