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
  // Intuitively obvious, so we can use assert by reveal
  assert s + [c] == s[..|s|] + [c];
}

lemma stringEquality(a: string, b: string)
  requires forall i :: 0 <= i < |a| ==> a[i] == b[i]
  requires |a| == |b|
  ensures a == b
{
  // Strings with same length and same characters at all positions are equal
  if |a| == 0 {
    assert a == "" && b == "";
  } else {
    assert a[0] == b[0];
    assert a[1..] == b[1..];
    stringEquality(a[1..], b[1..]);
  }
}

lemma countCharNonNegative(s: string, c: char)
  ensures countChar(s, c) >= 0
{
  // Cardinality of a set is always non-negative
}

lemma countCharSliceProperties(s: string, i: nat, c: char)
  requires i <= |s|
  ensures countChar(s[..i], c) == |set j | 0 <= j < i && j < |s| && s[j] == c|
{
  // By definition of countChar and string slicing
  var sliced := s[..i];
  assert forall j :: 0 <= j < |sliced| ==> sliced[j] == s[j];
  assert |sliced| == if i <= |s| then i else |s|;
}

lemma countCharSliceUpdate(s: string, i: nat, c: char)
  requires i < |s|
  ensures countChar(s[..i+1], c) == countChar(s[..i], c) + (if s[i] == c then 1 else 0)
{
  var prefix := s[..i];
  var extended := prefix + [s[i]];
  assert extended == s[..i+1] by {
    assert |extended| == i + 1;
    assert forall j :: 0 <= j < i ==> extended[j] == prefix[j] == s[j];
    assert extended[i] == s[i];
  }
  
  if s[i] == c {
    countCharProperties(prefix, c, 'z');
  } else {
    var dummy: char := if c == 'x' then 'y' else 'x';
    countCharProperties(prefix, c, dummy);
  }
}

lemma countCharFullString(s: string, c: char)
  ensures countChar(s[..|s|], c) == countChar(s, c)
{
  // s[..|s|] == s, so count must be the same
  assert s[..|s|] == s;
}

lemma countCharEmptySlice(s: string, c: char)
  ensures countChar(s[..0], c) == 0
{
}
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
      countCharSliceUpdate(s, i, 'x');
      countX := countX + 1;
    } else {
      assert s[i] == 'y';
      countCharSliceUpdate(s, i, 'y');
      countY := countY + 1;
    }
    i := i + 1;
  }
  
  countCharFullString(s, 'x');
  countCharFullString(s, 'y');
  
  var diff: int := if countX > countY then countX - countY else countY - countX;
  result := "";
  var j: nat := 0;
  
  while j < diff
    invariant j <= diff
    invariant |result| == j
    invariant countX > countY ==> forall k :: 0 <= k < j ==> result[k] == 'x'
    invariant countY > countX ==> forall k :: 0 <= k < j ==> result[k] == 'y'
  {
    if countX > countY {
      result := result + ['x'];
    } else {
      result := result + ['y'];
    }
    j := j + 1;
  }
  
  // Verify final postcondition
  var countX_final := countChar(s, 'x');
  var countY_final := countChar(s, 'y');
  assert countX_final == countX;
  assert countY_final == countY;
}
// </vc-code>

