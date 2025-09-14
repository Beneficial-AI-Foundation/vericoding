predicate ValidInput(s: string) {
    forall i :: 0 <= i < |s| ==> s[i] == 'L' || s[i] == 'R' || s[i] == 'U' || s[i] == 'D'
}

function abs(x: int): int
    ensures abs(x) >= 0
    ensures abs(x) == x || abs(x) == -x
{
    if x >= 0 then x else -x
}

function countChar(s: string, c: char): int
    requires 0 <= |s|
    ensures 0 <= countChar(s, c) <= |s|
    ensures countChar(s, c) == countCharHelper(s, c, 0, 0)
{
    countCharHelper(s, c, 0, 0)
}

function countCharHelper(s: string, c: char, index: int, count: int): int
    requires 0 <= index <= |s|
    requires count >= 0
    requires count + (|s| - index) >= 0
    decreases |s| - index
    ensures countCharHelper(s, c, index, count) >= count
    ensures countCharHelper(s, c, index, count) <= count + (|s| - index)
{
    if index == |s| then count
    else if s[index] == c then countCharHelper(s, c, index + 1, count + 1)
    else countCharHelper(s, c, index + 1, count)
}

function countCharFromIndex(s: string, c: char, index: int): int
    requires 0 <= index <= |s|
    ensures 0 <= countCharFromIndex(s, c, index) <= |s| - index
    decreases |s| - index
{
    if index == |s| then 0
    else if s[index] == c then 1 + countCharFromIndex(s, c, index + 1)
    else countCharFromIndex(s, c, index + 1)
}

predicate CorrectResult(s: string, result: int) {
    (|s| % 2 != 0 ==> result == -1) &&
    (|s| % 2 == 0 ==> result >= 0) &&
    (|s| % 2 == 0 ==> result <= |s| / 2) &&
    (|s| % 2 == 0 ==> result == (abs(countChar(s, 'L') - countChar(s, 'R')) + abs(countChar(s, 'U') - countChar(s, 'D'))) / 2)
}

// <vc-helpers>
lemma Lemma_Helper_Additivity(s: string, c: char, index: int, count: int)
  requires 0 <= index <= |s|
  requires count >= 0
  ensures countCharHelper(s, c, index, count) == count + countCharFromIndex(s, c, index)
  decreases |s| - index
{
  if index == |s| {
  } else {
    if s[index] == c {
      Lemma_Helper_Additivity(s, c, index + 1, count + 1);
      assert countCharFromIndex(s, c, index) == 1 + countCharFromIndex(s, c, index + 1);
      assert countCharHelper(s, c, index, count) == countCharHelper(s, c, index + 1, count + 1);
      assert countCharHelper(s, c, index + 1, count + 1) == (count + 1) + countCharFromIndex(s, c, index + 1);
    } else {
      Lemma_Helper_Additivity(s, c, index + 1, count);
      assert countCharFromIndex(s, c, index) == countCharFromIndex(s, c, index + 1);
      assert countCharHelper(s, c, index, count) == countCharHelper(s, c, index + 1, count);
      assert countCharHelper(s, c, index + 1, count) == count + countCharFromIndex(s, c, index + 1);
    }
  }
}

lemma Lemma_CountFromIndex0_Equals_CountChar(s: string, c: char)
  ensures countCharFromIndex(s, c, 0) == countChar(s, c)
{
  Lemma_Helper_Additivity(s, c, 0, 0);
  assert countCharHelper(s, c, 0, 0) == countCharFromIndex(s, c, 0);
  assert countChar(s, c) == countCharHelper(s, c, 0, 0);
}

lemma Lemma_CountSum_FromIndex(s: string, index: int)
  requires 0 <= index <= |s|
  requires forall i :: index <= i < |s| ==> s[i] == 'L' || s[i] == 'R' || s[i] == 'U' || s[i] == 'D'
  ensures countCharFromIndex(s, 'L', index) + countCharFromIndex(s, 'R', index) + countCharFromIndex(s, 'U', index) + countCharFromIndex(s, 'D', index) == |s| - index
  decreases |s| - index
{
  if index == |s| {
    assert countCharFromIndex(s, 'L', index) == 0;
    assert countCharFromIndex(s, 'R', index) == 0;
    assert countCharFromIndex(s, 'U', index) == 0;
    assert countCharFromIndex(s, 'D', index) == 0;
  } else {
    assert forall i :: index + 1 <= i < |s| ==> s[i] == 'L' || s[i] == 'R' || s[i] == 'U' || s[i] == 'D';
    Lemma_CountSum_FromIndex(s, index + 1);
    if s[index] == 'L' {
      assert countCharFromIndex(s, 'L', index) == 1 + countCharFromIndex(s, 'L', index + 1);
      assert countCharFromIndex(s, 'R', index) == countCharFromIndex(s, 'R', index + 1);
      assert countCharFromIndex(s, 'U', index) == countCharFromIndex(s, 'U', index + 1);
      assert countCharFromIndex(s, 'D', index) == countCharFromIndex(s, 'D', index + 1);
    } else if s[index] == 'R' {
      assert countCharFromIndex(s, 'L', index) == countCharFromIndex(s, 'L', index + 1);
      assert countCharFromIndex(s, 'R', index) == 1 + countCharFromIndex(s, 'R', index + 1);
      assert countCharFromIndex(s, 'U', index) == countCharFromIndex(s, 'U', index + 1);
      assert countCharFromIndex(s, 'D', index) == countCharFromIndex(s, 'D', index + 1);
    } else if s[index] == 'U' {
      assert countCharFromIndex(s, 'L', index) == countCharFromIndex(s, 'L', index + 1);
      assert countCharFromIndex(s, 'R', index) == countCharFromIndex(s, 'R', index + 1);
      assert countCharFromIndex(s, 'U', index) == 1 + countCharFromIndex(s, 'U', index + 1);
      assert countCharFromIndex(s, 'D', index) == countCharFromIndex(s, 'D', index + 1);
    } else {
      assert s[index] == 'D';
      assert countCharFromIndex(s, 'L', index) == countCharFromIndex(s, 'L', index + 1);
      assert countCharFromIndex(s, 'R', index) == countCharFromIndex(s, 'R', index + 1);
      assert countCharFromIndex(s, 'U', index) == countCharFromIndex(s, 'U', index + 1);
      assert countCharFromIndex(s, 'D', index) == 1 + countCharFromIndex(s, 'D', index + 1);
    }
  }
}

lemma Lemma_AbsLeqSum(a: int, b: int)
  requires 0 <= a && 0 <= b
  ensures abs(a - b) <= a + b
{
  if a >= b {
    assert abs(a - b) == a - b;
    assert a - b <= a + b;
  } else {
    assert abs(a - b) == b - a;
    assert b - a <= a + b;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures CorrectResult(s, result)
// </vc-spec>
// <vc-code>
{
  if |s| % 2 != 0 {
    result := -1;
  } else {
    var l := countChar(s, 'L');
    var r := countChar(s, 'R');
    var u := countChar(s, 'U');
    var d := countChar(s, 'D');

    // Sum of counts equals length (using ValidInput)
    Lemma_CountSum_FromIndex(s, 0);
    Lemma_CountFromIndex0_Equals_CountChar(s, 'L');
    Lemma_CountFromIndex0_Equals_CountChar(s, 'R');
    Lemma_CountFromIndex0_Equals_CountChar(s, 'U');
    Lemma_CountFromIndex0_Equals_CountChar(s, 'D');
    assert countCharFromIndex(s, 'L', 0) == l;
    assert countCharFromIndex(s, 'R', 0) == r;
    assert countCharFromIndex(s, 'U', 0) == u;
    assert countCharFromIndex(s, 'D', 0) == d;
    assert l + r + u + d == |s|;

    result := (abs(l - r) + abs(u - d)) / 2;

    // Nonnegativity and upper bound
    Lemma_AbsLeqSum(l, r);
    Lemma_AbsLeqSum(u, d);
    assert 0 <= abs(l - r);
    assert 0 <= abs(u - d);
    assert abs(l - r) + abs(u - d) <= (l + r) + (u + d);
    assert abs(l - r) + abs(u - d) <= |s|;
  }
}
// </vc-code>

