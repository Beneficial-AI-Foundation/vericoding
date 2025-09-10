predicate ValidOutput(n: int, result: seq<string>)
    requires n >= 2
{
    if n < 6 then
        |result| == 1 + (n - 1) &&
        result[0] == "-1" &&
        (forall i :: 1 <= i < |result| ==> result[i] == "1 " + IntToString(i + 1))
    else
        |result| == (5 + (n - 6)) + (n - 1) &&
        result[0] == "1 2" && result[1] == "1 3" && result[2] == "1 4" && 
        result[3] == "2 5" && result[4] == "2 6" &&
        (forall i :: 5 <= i < 5 + (n - 6) ==> result[i] == "1 " + IntToString(i + 2)) &&
        (forall i :: 5 + (n - 6) <= i < |result| ==> result[i] == "1 " + IntToString(i - (5 + (n - 6)) + 2))
}

function IntToString(n: int): string
    decreases n < 0, if n >= 0 then n else -n
{
    if n < 0 then "-" + IntToString(-n)
    else if n < 10 then [n as char + '0']
    else IntToString(n / 10) + IntToString(n % 10)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<string>)
    requires n >= 2
    ensures ValidOutput(n, result)
// </vc-spec>
// <vc-code>
var result: seq<string> := [];
  if n < 6 {
    result := result + ["-1"];
    var i := 2;
    while i <= n 
    {
      result := result + ["1 " + IntToString(i)];
      i := i + 1;
    }
  } else {
    result := ["1 2", "1 3", "1 4", "2 5", "2 6"];
    var count := n - 6;
    var start := 7;
    var k := 0;
    while k < count 
    {
      result := result + ["1 " + IntToString(start)];
      start := start + 1;
      k := k + 1;
    }
    var i := 2;
    while i <= n 
    {
      result := result + ["1 " + IntToString(i)];
      i := i + 1;
    }
  }
// </vc-code>

