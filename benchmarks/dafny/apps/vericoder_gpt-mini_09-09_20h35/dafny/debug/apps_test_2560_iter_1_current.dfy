predicate ValidInput(input: string)
{
    |input| > 0
}

function CanMakeSum(n: int, l: int, r: int): bool
{
    l > 0 && l <= r && n > 0 && n % l <= (r - l) * (n / l)
}

predicate ValidOutput(result: string)
{
    |result| >= 0 && forall i :: 0 <= i < |result| ==> result[i] in "Yes\nNo\n "
}

predicate CorrectSolution(input: string, result: string)
{
    var lines := SplitLines(input);
    |lines| > 0 ==> 
    (var t := ParseInt(lines[0]);
     var outputLines := SplitLines(result);
     |outputLines| >= 1 && (|outputLines| == 1 ==> outputLines[0] == "") &&
     (|outputLines| > 1 ==> outputLines[|outputLines|-1] == "") &&
     forall i :: 1 <= i <= t && i < |lines| ==>
        (var parts := SplitSpaces(lines[i]);
         |parts| >= 3 ==>
         (var n := ParseInt(parts[0]);
          var l := ParseInt(parts[1]);
          var r := ParseInt(parts[2]);
          var expectedOutput := if CanMakeSum(n, l, r) then "Yes" else "No";
          i-1 < |outputLines| && outputLines[i-1] == expectedOutput)))
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
    ensures CorrectSolution(input, result)
// </vc-spec>
// <vc-code>
{
  var lines := SplitLines(input);
  var t := 0;
  if |lines| > 0 {
    t := ParseInt(lines[0]);
  }
  var res := "";
  var upto := t;
  if upto > |lines| - 1 {
    upto := |lines| - 1;
  }
  var i := 1;
  while i <= upto
    decreases upto - i
  {
    var parts := SplitSpaces(lines[i]);
    if |parts| >= 3 {
      var n := ParseInt(parts[0]);
      var l := ParseInt(parts[1]);
      var r := ParseInt(parts[2]);
      var expected := if CanMakeSum(n, l, r) then "Yes" else "No";
      res := res + expected + "\n";
    } else {
      res := res + "" + "\n";
    }
    i := i + 1;
  }
  result := res;
}
// </vc-code>

