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
lemma countCharProperties(s: string, c: char, d: char)
  ensures countChar(s + [c], c) == countChar(s, c) + 1
  ensures c != d ==> countChar(s + [d], c) == countChar(s, c)
{
}

lemma stringEquality(a: string, b: string)
  requires forall i :: 0 <= i < |a| ==> a[i] == b[i]
  requires |a| == |b|
  ensures a == b
{
}

lemma countCharNonNegative(s: string, c: char)
  ensures countChar(s, c) >= 0
{
}

lemma countCharSliceProperties(s: string, i: nat, c: char)
  requires i <= |s|
  ensures countChar(s[..i], c) == |set j | 0 <= j < i && j < |s| && s[j] == c|
{
}

lemma countCharSliceUpdate(s: string, i: nat, c: char)
  requires i < |s|
  ensures countChar(s[..i+1], c) == countChar(s[..i], c) + (if s[i] == c then 1 else 0)
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidOutput(s, result)
// </vc-spec>
// <vc-code>
{
  var i: nat := 0;
  var countX: nat := 0;
  var countY: nat := 0;
  
  while i < |s|
    invariant i <= |s|
    invariant countX == countChar(s[..i], 'x')
    invariant countY == countChar(s[..i], 'y')
  {
    if s[i] == 'x' {
      countX := countX + 1;
    } else if s[i] == 'y' {
      countY := countY + 1;
    }
    i := i + 1;
  }
  
  var diff: int := if countX > countY then countX - countY else countY - countX;
  result := "";
  var j: nat := 0;
  
  while j < diff
    invariant j <= diff
    invariant |result| == j
    invariant (countX > countY ==> forall k :: 0 <= k < j ==> result[k] == 'x')
    invariant (countY > countX ==> forall k :: 0 <= k < j ==> result[k] == 'y')
  {
    if countX > countY {
      result := result + ['x'];
    } else {
      result := result + ['y'];
    }
    j := j + 1;
  }
}
// </vc-code>

