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
method BuildXs(n: nat) returns (r: string)
  ensures |r| == n
  ensures forall i :: 0 <= i < |r| ==> r[i] == 'x'
{
  var res := "";
  var k: nat := 0;
  while k < n
    invariant 0 <= k <= n
    invariant |res| == k
    invariant forall i :: 0 <= i < |res| ==> res[i] == 'x'
    decreases n - k
  {
    res := res + "x";
    k := k + 1;
  }
  r := res;
}

method BuildYs(n: nat) returns (r: string)
  ensures |r| == n
  ensures forall i :: 0 <= i < |r| ==> r[i] == 'y'
{
  var res := "";
  var k: nat := 0;
  while k < n
    invariant 0 <= k <= n
    invariant |res| == k
    invariant forall i :: 0 <= i < |res| ==> res[i] == 'y'
    decreases n - k
  {
    res := res + "y";
    k := k + 1;
  }
  r := res;
}
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
    result := BuildYs(countY - countX);
  } else {
    result := BuildXs(countX - countY);
  }
}
// </vc-code>

