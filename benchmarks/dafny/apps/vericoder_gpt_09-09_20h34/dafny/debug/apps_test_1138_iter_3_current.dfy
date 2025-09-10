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
lemma AbsDiffLeqSum(x: int, y: int)
  requires 0 <= x && 0 <= y
  ensures abs(x - y) <= x + y
{
  if x >= y {
    assert abs(x - y) == x - y;
    assert x - y <= x;
    assert x <= x + y;
  } else {
    assert abs(x - y) == y - x;
    assert y - x <= y;
    assert y <= x + y;
  }
}

lemma CountCharHelperRel(s: string, c: char, index: int, acc: int)
  requires 0 <= index <= |s|
  requires acc >= 0
  requires acc + (|s| - index) >= 0
  ensures countCharHelper(s, c, index, acc) == acc + countCharFromIndex(s, c, index)
  decreases |s| - index
{
  if index == |s| {
    assert countCharFromIndex(s, c, index) == 0;
  } else {
    if s[index] == c {
      assert countCharFromIndex(s, c, index) == 1 + countCharFromIndex(s, c, index + 1);
      assert countCharHelper(s, c, index, acc) == countCharHelper(s, c, index + 1, acc + 1);
      assert countCharHelper(s, c, index + 1, acc + 1) == (acc + 1) + countCharFromIndex(s, c, index + 1);
      assert acc + (1 + countCharFromIndex(s, c, index + 1)) == acc + countCharFromIndex(s, c, index);
    } else {
      assert countCharFromIndex(s, c, index) == countCharFromIndex(s, c, index + 1);
      assert countCharHelper(s, c, index, acc) == countCharHelper(s, c, index + 1, acc);
      assert countCharHelper(s, c, index + 1, acc) == acc + countCharFromIndex(s, c, index + 1);
      assert acc + countCharFromIndex(s, c, index + 1) == acc + countCharFromIndex(s, c, index);
    }
  }
}

lemma CountSumFromIndex(s: string, i: int)
  requires ValidInput(s)
  requires 0 <= i <= |s|
  ensures countCharFromIndex(s, 'L', i) + countCharFromIndex(s, 'R', i) + countCharFromIndex(s, 'U', i) + countCharFromIndex(s, 'D', i) == |s| - i
  decreases |s| - i
{
  if i == |s| {
  } else {
    assert 0 <= i < |s|;
    assert s[i] == 'L' || s[i] == 'R' || s[i] == 'U' || s[i] == 'D';
    if s[i] == 'L' {
      assert countCharFromIndex(s, 'L', i) == 1 + countCharFromIndex(s, 'L', i + 1);
      assert countCharFromIndex(s, 'R', i) == countCharFromIndex(s, 'R', i + 1);
      assert countCharFromIndex(s, 'U', i) == countCharFromIndex(s, 'U', i + 1);
      assert countCharFromIndex(s, 'D', i) == countCharFromIndex(s, 'D', i + 1);
      CountSumFromIndex(s, i + 1);
      assert countCharFromIndex(s, 'L', i) + countCharFromIndex(s, 'R', i) + countCharFromIndex(s, 'U', i) + countCharFromIndex(s, 'D', i)
             == 1 + (countCharFromIndex(s, 'L', i + 1) + countCharFromIndex(s, 'R', i + 1) + countCharFromIndex(s, 'U', i + 1) + countCharFromIndex(s, 'D', i + 1));
      assert 1 + (|s| - (i + 1)) == |s| - i;
    } else if s[i] == 'R' {
      assert countCharFromIndex(s, 'L', i) == countCharFromIndex(s, 'L', i + 1);
      assert countCharFromIndex(s, 'R', i) == 1 + countCharFromIndex(s, 'R', i + 1);
      assert countCharFromIndex(s, 'U', i) == countCharFromIndex(s, 'U', i + 1);
      assert countCharFromIndex(s, 'D', i) == countCharFromIndex(s, 'D', i + 1);
      CountSumFromIndex(s, i + 1);
      assert countCharFromIndex(s, 'L', i) + countCharFromIndex(s, 'R', i) + countCharFromIndex(s, 'U', i) + countCharFromIndex(s, 'D', i)
             == 1 + (countCharFromIndex(s, 'L', i + 1) + countCharFromIndex(s, 'R', i + 1) + countCharFromIndex(s, 'U', i + 1) + countCharFromIndex(s, 'D', i + 1));
      assert 1 + (|s| - (i + 1)) == |s| - i;
    } else if s[i] == 'U' {
      assert countCharFromIndex(s, 'L', i) == countCharFromIndex(s, 'L', i + 1);
      assert countCharFromIndex(s, 'R', i) == countCharFromIndex(s, 'R', i + 1);
      assert countCharFromIndex(s, 'U', i) == 1 + countCharFromIndex(s, 'U', i + 1);
      assert countCharFromIndex(s, 'D', i) == countCharFromIndex(s, 'D', i + 1);
      CountSumFromIndex(s, i + 1);
      assert countCharFromIndex(s, 'L', i) + countCharFromIndex(s, 'R', i) + countCharFromIndex(s, 'U', i) + countCharFromIndex(s, 'D', i)
             == 1 + (countCharFromIndex(s, 'L', i + 1) + countCharFromIndex(s, 'R', i + 1) + countCharFromIndex(s, 'U', i + 1) + countCharFromIndex(s, 'D', i + 1));
      assert 1 + (|s| - (i + 1)) == |s| - i;
    } else {
      assert countCharFromIndex(s, 'L', i) == countCharFromIndex(s, 'L', i + 1);
      assert countCharFromIndex(s, 'R', i) == countCharFromIndex(s, 'R', i + 1);
      assert countCharFromIndex(s, 'U', i) == countCharFromIndex(s, 'U
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures CorrectResult(s, result)
// </vc-spec>
// <vc-code>
lemma AbsDiffLeqSum(x: int, y: int)
  requires 0 <= x && 0 <= y
  ensures abs(x - y) <= x + y
{
  if x >= y {
    assert abs(x - y) == x - y;
    assert x - y <= x;
    assert x <= x + y;
  } else {
    assert abs(x - y) == y - x;
    assert y - x <= y;
    assert y <= x + y;
  }
}

lemma CountCharHelperRel(s: string, c: char, index: int, acc: int)
  requires 0 <= index <= |s|
  requires acc >= 0
  requires acc + (|s| - index) >= 0
  ensures countCharHelper(s, c, index, acc) == acc + countCharFromIndex(s, c, index)
  decreases |s| - index
{
  if index == |s| {
    assert countCharFromIndex(s, c, index) == 0;
  } else {
    if s[index] == c {
      assert countCharFromIndex(s, c, index) == 1 + countCharFromIndex(s, c, index + 1);
      assert countCharHelper(s, c, index, acc) == countCharHelper(s, c, index + 1, acc + 1);
      assert countCharHelper(s, c, index + 1, acc + 1) == (acc + 1) + countCharFromIndex(s, c, index + 1);
      assert acc + (1 + countCharFromIndex(s, c, index + 1)) == acc + countCharFromIndex(s, c, index);
    } else {
      assert countCharFromIndex(s, c, index) == countCharFromIndex(s, c, index + 1);
      assert countCharHelper(s, c, index, acc) == countCharHelper(s, c, index + 1, acc);
      assert countCharHelper(s, c, index + 1, acc) == acc + countCharFromIndex(s, c, index + 1);
      assert acc + countCharFromIndex(s, c, index + 1) == acc + countCharFromIndex(s, c, index);
    }
  }
}

lemma CountSumFromIndex(s: string, i: int)
  requires ValidInput(s)
  requires 0 <= i <= |s|
  ensures countCharFromIndex(s, 'L', i) + countCharFromIndex(s, 'R', i) + countCharFromIndex(s, 'U', i) + countCharFromIndex(s, 'D', i) == |s| - i
  decreases |s| - i
{
  if i == |s| {
  } else {
    assert 0 <= i < |s|;
    assert s[i] == 'L' || s[i] == 'R' || s[i] == 'U' || s[i] == 'D';
    if s[i] == 'L' {
      assert countCharFromIndex(s, 'L', i) == 1 + countCharFromIndex(s, 'L', i + 1);
      assert countCharFromIndex(s, 'R', i) == countCharFromIndex(s, 'R', i + 1);
      assert countCharFromIndex(s, 'U', i) == countCharFromIndex(s, 'U', i + 1);
      assert countCharFromIndex(s, 'D', i) == countCharFromIndex(s, 'D', i + 1);
      CountSumFromIndex(s, i + 1);
      assert countCharFromIndex(s, 'L', i) + countCharFromIndex(s, 'R', i) + countCharFromIndex(s, 'U', i) + countCharFromIndex(s, 'D', i)
             == 1 + (countCharFromIndex(s, 'L', i + 1) + countCharFromIndex(s, 'R', i + 1) + countCharFromIndex(s, 'U', i + 1) + countCharFromIndex(s, 'D', i + 1));
      assert 1 + (|s| - (i + 1)) == |s| - i;
    } else if s[i] == 'R' {
      assert countCharFromIndex(s, 'L', i) == countCharFromIndex(s, 'L', i + 1);
      assert countCharFromIndex(s, 'R', i) == 1 + countCharFromIndex(s, 'R', i + 1);
      assert countCharFromIndex(s, 'U', i) == countCharFromIndex(s, 'U', i + 1);
      assert countCharFromIndex(s, 'D', i) == countCharFromIndex(s, 'D', i + 1);
      CountSumFromIndex(s, i + 1);
      assert countCharFromIndex(s, 'L', i) + countCharFromIndex(s, 'R', i) + countCharFromIndex(s, 'U', i) + countCharFromIndex(s, 'D', i)
             == 1 + (countCharFromIndex(s, 'L', i + 1) + countCharFromIndex(s, 'R', i + 1) + countCharFromIndex(s, 'U', i + 1) + countCharFromIndex(s, 'D', i + 1));
      assert 1 + (|s| - (i + 1)) == |s| - i;
    } else if s[i] == 'U' {
      assert countCharFromIndex(s, 'L', i) == countCharFromIndex(s, 'L', i + 1);
      assert countCharFromIndex(s, 'R', i) == countCharFromIndex(s, 'R', i + 1);
      assert countCharFromIndex(s, 'U', i) == 1 + countCharFromIndex(s, 'U', i + 1);
      assert countCharFromIndex(s, 'D', i) == countCharFromIndex(s, 'D', i + 1);
      CountSumFromIndex(s, i + 1);
      assert countCharFromIndex(s, 'L', i) + countCharFromIndex(s, 'R', i) + countCharFromIndex(s, 'U', i) + countCharFromIndex(s, 'D', i)
             == 1 + (countCharFromIndex(s, 'L', i + 1) + countCharFromIndex(s, 'R', i + 1) + countCharFromIndex(s, 'U', i + 1) + countCharFromIndex(s, 'D', i + 1));
      assert 1 + (|s| - (i + 1)) == |s| - i;
    } else {
      assert countCharFromIndex(s, 'L', i) == countCharFromIndex(s, 'L', i + 1);
      assert countCharFromIndex(s, 'R', i) == countCharFromIndex(s, 'R', i + 1);
      assert countCharFromIndex(s, 'U', i) == countCharFromIndex(s, 'U
// </vc-code>

