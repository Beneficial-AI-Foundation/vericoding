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
lemma CountCharHelperRel(s: string, c: char, index: int, count: int)
    requires 0 <= index <= |s|
    requires count >= 0
    decreases |s| - index
    ensures countCharHelper(s, c, index, count) == count + countCharFromIndex(s, c, index)
{
    if index == |s| {
        assert countCharHelper(s, c, index, count) == count;
        assert countCharFromIndex(s, c, index) == 0;
    } else {
        if s[index] == c {
            CountCharHelperRel(s, c, index + 1, count + 1);
            // unfold definitions
            assert countCharHelper(s, c, index, count) == countCharHelper(s, c, index + 1, count + 1);
            assert countCharHelper(s, c, index + 1, count + 1) == (count + 1) + countCharFromIndex(s, c, index + 1);
            assert countCharFromIndex(s, c, index) == 1 + countCharFromIndex(s, c, index + 1);
            assert countCharHelper(s, c, index, count) == count + countCharFromIndex(s, c, index);
        } else {
            CountCharHelperRel(s, c, index + 1, count);
            assert countCharHelper(s, c, index, count) == countCharHelper(s, c, index + 1, count);
            assert countCharHelper(s, c, index + 1, count) == count + countCharFromIndex(s, c, index + 1);
            assert countCharFromIndex(s, c, index) == countCharFromIndex(s, c, index + 1);
            assert countCharHelper(s, c, index, count) == count + countCharFromIndex(s, c, index);
        }
    }
}

lemma CountSumFromIndex(s: string, index: int)
    requires ValidInput(s)
    requires 0 <= index <= |s|
    decreases |s| - index
    ensures countCharFromIndex(s, 'L', index) + countCharFromIndex(s, 'R', index) + countCharFromIndex(s, 'U', index) + countCharFromIndex(s, 'D', index) == |s| - index
{
    if index == |s| {
        assert countCharFromIndex(s, 'L', index) == 0;
        assert countCharFromIndex(s, 'R', index) == 0;
        assert countCharFromIndex(s, 'U', index) == 0;
        assert countCharFromIndex(s, 'D', index) == 0;
    } else {
        var c := s[index];
        CountSumFromIndex(s, index + 1);
        if c == 'L' {
            assert countCharFromIndex(s, 'L', index) == 1 + countCharFromIndex(s, 'L', index + 1);
            assert countCharFromIndex(s, 'R', index) == countCharFromIndex(s, 'R', index + 1);
            assert countCharFromIndex(s, 'U', index) == countCharFromIndex(s, 'U', index + 1);
            assert countCharFromIndex(s, 'D', index) == countCharFromIndex(s, 'D', index + 1);
            assert countCharFromIndex(s, 'L', index) + countCharFromIndex(s, 'R', index) + countCharFromIndex(s, 'U', index) + countCharFromIndex(s, 'D', index) ==
                   1 + (|s| - (index + 1));
        } else if c == 'R' {
            assert countCharFromIndex(s, 'L', index) == countCharFromIndex(s, 'L', index + 1);
            assert countCharFromIndex(s, 'R', index) == 1 + countCharFromIndex(s, 'R', index + 1);
            assert countCharFromIndex(s, 'U', index) == countCharFromIndex(s, 'U', index + 1);
            assert countCharFromIndex(s, 'D', index) == countCharFromIndex(s, 'D', index + 1);
            assert countCharFromIndex(s, 'L', index) + countCharFromIndex(s, 'R', index) + countCharFromIndex(s, 'U', index) + countCharFromIndex(s, 'D', index) ==
                   1 + (|s| - (index + 1));
        } else if c == 'U' {
            assert countCharFromIndex(s, 'L', index) == countCharFromIndex(s, 'L', index + 1);
            assert countCharFromIndex(s, 'R', index) == countCharFromIndex(s, 'R', index + 1);
            assert countCharFromIndex(s, 'U', index) == 1 + countCharFromIndex(s, 'U', index + 1);
            assert countCharFromIndex(s, 'D', index) == countCharFromIndex(s, 'D', index + 1);
            assert countCharFromIndex(s, 'L', index) + countCharFromIndex(s, 'R', index) + countCharFromIndex(s, 'U', index) + countCharFromIndex(s, 'D', index) ==
                   1 + (|s| - (index + 1));
        } else {
            // c == 'D'
            assert countCharFromIndex(s, 'L', index) == countCharFromIndex(s, 'L', index + 1);
            assert countCharFromIndex(s, 'R', index) == countCharFromIndex(s, 'R', index + 1);
            assert countCharFromIndex(s, 'U', index) == countCharFromIndex(s, 'U', index + 1);
            assert countCharFromIndex(s, 'D', index) == 1 + countCharFromIndex(s, 'D', index + 1);
            assert countCharFromIndex(s, 'L', index) + countCharFromIndex(s, 'R', index) + countCharFromIndex(s, 'U', index) + countCharFromIndex(s, 'D', index) ==
                   1 + (|s| - (index + 1));
        }
        assert 1 + (|s| - (index + 1)) == |s| - index;
    }
}

lemma CountSumEqualsLength(s: string)
    requires ValidInput(s)
    ensures countChar(s, 'L') + countChar(s, 'R') + countChar(s, 'U') + countChar(s, 'D') == |s|
{
    // relate countChar(s, c) to countCharFromIndex(s, c, 0)
    CountCharHelperRel(s, 'L', 0, 0);
    CountCharHelperRel(s, 'R', 0, 0);
    CountCharHelperRel(s, 'U', 0, 0);
    CountCharHelperRel(s, 'D', 0, 0);
    // countChar(s,c) == countCharFromIndex(s,c,0)
    assert countChar(s, 'L') == countCharFromIndex(s, 'L', 0);
    assert countChar(s, 'R') == countCharFromIndex(s, 'R', 0);
    assert countChar(s, 'U') == countCharFromIndex(s, 'U', 0);
    assert countChar(s, 'D') == countCharFromIndex(s, 'D', 0);
    // sum from index 0 equals |s|
    CountSumFromIndex(s, 0);
    assert countCharFromIndex(s, 'L', 0) + countCharFromIndex(s, 'R', 0) + countCharFromIndex(s, 'U', 0) + countCharFromIndex(s, 'D', 0) == |s| - 0;
    // conclude
    assert countChar(s, 'L') + countChar(s, 'R') + countChar(s, 'U') + countChar(s, 'D') == |s|;
}

lemma AbsSubtractBound(a: int, b: int)
    requires a >= 0 && b >= 0
    ensures abs(a - b) <= a + b
{
    if a >= b {
        // abs(a-b) = a-b <= a+b
    } else {
        // abs(a-b) = b-a <= a+b
    }
}

lemma AbsSumLeLength(s: string)
    requires ValidInput(s)
    ensures abs(countChar(s, 'L') - countChar(s, 'R')) + abs(countChar(s, 'U') - countChar(s, 'D')) <= |s|
{
    var l := countChar(s, 'L');
    var r := countChar(s, 'R');
    var u := countChar(s, 'U');
    var d := countChar(s, 'D');
    AbsSubtractBound(l, r);
    AbsSubtractBound(u, d);
    CountSumEqualsLength(s);
    assert abs(l - r) <= l + r;
    assert abs(u - d) <= u + d;
    assert abs(l - r) + abs(u - d) <= (l + r) + (u + d);
    assert (l + r) + (u + d) == |s|;
}

lemma Div2LowerBound(a: int)
    requires a >= 0
    ensures 2*(a / 2) <= a
{
    // Use division remainder property: a == 2*(a/2) + a%2 and a%2 >= 0
    assert a == 2*(a / 2) + a % 2;
    assert a % 2 >= 0;
    assert 2*(a / 2) <= a;
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
    return;
  }
  var l := countChar(s, 'L');
  var r := countChar(s, 'R');
  var u := countChar(s, 'U');
  var d := countChar(s, 'D');
  AbsSumLeLength(s);
  var num := abs(l - r) + abs(u - d);
  Div2LowerBound(num);
  result := num / 2;
  // help the verifier with obvious bounds
  assert result >= 0;
  assert 2 * result <= num;
  assert num <= |s|;
  assert 2 * result <= |s|;
}
// </vc-code>

