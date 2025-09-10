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
  if countY > countX {
    var n: nat := countY - countX;
    var r := "";
    while |r| < n
      invariant |r| <= n
      invariant forall i :: 0 <= i < |r| ==> r[i] == 'y'
      decreases n - |r|
    {
      r := r + "y";
    }
    result := r;
  } else {
    var n: nat := countX - countY;
    var r := "";
    while |r| < n
      invariant |r| <= n
      invariant forall i :: 0 <= i < |r| ==> r[i] == 'x'
      decreases n - |r|
    {
      r := r + "x";
    }
    result := r;
  }
}
// </vc-code>

