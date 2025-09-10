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
function countPrefix(s: string, i: int, c: char): nat
  requires 0 <= i <= |s|
{
  |set j | 0 <= j < i && s[j] == c|
}

lemma CountPrefixFull(s: string, c: char)
  ensures countPrefix(s, |s|, c) == countChar(s, c)
{
  assert countPrefix(s, |s|, c) == |set j | 0 <= j < |s| && s[j] == c|;
  assert countChar(s, c) == |set j | 0 <= j < |s| && s[j] == c|;
}

lemma CountPrefixStep(s: string, i: int, c: char)
  requires 0 <= i < |s|
  ensures countPrefix(s, i + 1, c) == countPrefix(s, i, c) + (if s[i] == c then 1 else 0)
{
  var A := set j | 0 <= j < i && s[j] == c;
  var B := set j | 0 <= j < i + 1 && s[j] == c;
  assert countPrefix(s, i, c) == |A|;
  assert countPrefix(s, i + 1, c) == |B|;
  if s[i] == c {
    assert i < |s|;
    assert i !in A;
    assert B == A + {i};
    assert |B| == |A| + 1;
  } else {
    assert B == A;
    assert |B| == |A|;
  }
  assert countPrefix(s, i + 1, c) == countPrefix(s, i, c) + (if s[i] == c then 1 else 0);
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidOutput(s, result)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var cntX := 0;
  var cntY := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= cntX && 0 <= cntY
    invariant cntX == countPrefix(s, i, 'x')
    invariant cntY == countPrefix(s, i, 'y')
  {
    var oldI := i;
    if s[oldI] == 'x' {
      cntX := cntX + 1;
    } else {
      cntY := cntY + 1;
    }
    CountPrefixStep(s, oldI, 'x');
    CountPrefixStep(s, oldI, 'y');
    i := oldI + 1;
  }

  // Relate computed prefix counts to countChar
  CountPrefixFull(s, 'x');
  CountPrefixFull(s, 'y');
  assert cntX == countPrefix(s, |s|, 'x');
  assert cntY == countPrefix(s, |s|, 'y');
  assert cntX == countChar(s, 'x');
  assert cntY == countChar(s, 'y');

  var ch := if cntY > cntX then 'y' else 'x';
  var target := if cntY > cntX then cntY - cntX else cntX - cntY;

  var res := "";
  var k := 0;
  while k < target
    invariant 0 <= k <= target
    invariant |res| == k
    invariant forall t :: 0 <= t < |res| ==> res[t] == ch
  {
    if ch == 'x' {
      res := res + "x";
    } else {
      res := res + "y";
    }
    k := k + 1;
  }

  result := res;
}
// </vc-code>

