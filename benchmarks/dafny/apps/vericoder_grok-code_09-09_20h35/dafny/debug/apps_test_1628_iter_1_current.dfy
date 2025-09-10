predicate ValidInput(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> s[i] == 'x' || s[i] == 'y'
}

function countChar(s: string, c: char): nat
{
    |set i | 0 <= i < |s| && s[i] == c|
}

predicate ValidOutput(s: string, result: string)
    requires ValidInput(s)
{
    var countX := countChar(s, 'x');
    var countY := countChar(s, 'y');
    if countY > countX then
        |result| == countY - countX && forall i :: 0 <= i < |result| ==> result[i] == 'y'
    else
        |result| == countX - countY && forall i :: 0 <= i < |result| ==> result[i] == 'x'
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidOutput(s, result)
// </vc-spec>
// <vc-code>
{
  var countX := countChar(s, 'x');
  var countY := countChar(s, 'y');
  var diff : nat;
  var charToUse : char;
  if countY > countX {
    diff := countY - countX;
    charToUse := 'y';
  } else {
    diff := countX - countY;
    charToUse := 'x';
  }
  result := [];
  while diff > 0
    invariant |result| == old(diff) - diff
    invariant forall i :: 0 <= i < |result| ==> result[i] == charToUse
  {
    result := result + [charToUse];
    diff := diff - 1;
  }
}
// </vc-code>

