predicate ValidInput(s: string) 
{
    |s| == 7 && s[0] == 'A' && forall i :: 1 <= i < 7 ==> '0' <= s[i] <= '9'
}

function DigitSum(s: string, start: int, end: int): int
    requires 0 <= start <= end <= |s|
    requires forall i :: start <= i < end ==> '0' <= s[i] <= '9'
    decreases end - start
{
    if start >= end then 0
    else (s[start] as int - '0' as int) + DigitSum(s, start + 1, end)
}

function ZeroCount(s: string, start: int, end: int): int
    requires 0 <= start <= end <= |s|
    decreases end - start
{
    if start >= end then 0
    else (if s[start] == '0' then 1 else 0) + ZeroCount(s, start + 1, end)
}

// <vc-helpers>
lemma DigitSum_Append(s: string, start: int, end: int)
  requires 0 <= start < end <= |s|
  requires forall k :: start <= k < end ==> '0' <= s[k] <= '9'
  ensures DigitSum(s, start, end) == DigitSum(s, start, end - 1) + (s[end - 1] as int - '0' as int)
{
  if start + 1 == end {
    // base case
    assert DigitSum(s, start, end) == (s[start] as int - '0' as int);
    assert DigitSum(s, start, end - 1) == 0;
    assert DigitSum(s, start, end) == DigitSum(s, start, end - 1) + (s[end - 1] as int - '0' as int);
  } else {
    // unfold definitions
    assert DigitSum(s, start, end) == (s[start] as int - '0' as int) + DigitSum(s, start + 1, end);
    assert DigitSum(s, start, end - 1) == (s[start] as int - '0' as int) + DigitSum(s, start + 1, end - 1);
    DigitSum_Append(s, start + 1, end);
    assert DigitSum(s, start + 1, end) == DigitSum(s, start + 1, end - 1) + (s[end - 1] as int - '0' as int);
    assert DigitSum(s, start, end) == (s[start] as int - '0' as int) + (DigitSum(s, start + 1, end - 1) + (s[end - 1] as int - '0' as int));
    assert DigitSum(s, start, end) == ((s[start] as int - '0' as int) + DigitSum(s, start + 1, end - 1)) + (s[end - 1] as int - '0' as int);
    assert DigitSum(s, start, end) == DigitSum(s, start, end - 1) + (s[end - 1] as int - '0' as int);
  }
}

lemma ZeroCount_Append(s: string, start: int, end: int)
  requires 0 <= start < end <= |s|
  ensures ZeroCount(s, start, end) == ZeroCount(s, start, end - 1) + (if s[end - 1] == '0' then 1 else 0)
{
  if start + 1 == end {
    assert ZeroCount(s, start, end) == (if s[start] == '0' then 1 else 0);
    assert ZeroCount(s, start, end - 1) == 0;
    assert ZeroCount(s, start, end) == ZeroCount(s, start, end - 1) + (if s[end - 1] == '0' then 1 else 0);
  } else {
    assert ZeroCount(s, start, end) == (if s[start] == '0' then 1 else 0) + ZeroCount(s, start + 1, end);
    assert ZeroCount(s, start, end - 1) == (if s[start] == '0' then 1 else 0) + ZeroCount(s, start + 1, end - 1);
    ZeroCount_Append(s, start + 1, end);
    assert ZeroCount(s, start + 1, end) == ZeroCount(s, start + 1, end - 1) + (if s[end - 1] == '0' then 1 else 0);
    assert ZeroCount(s, start, end) == (if s[start] == '0' then 1 else 0) + (ZeroCount(s, start + 1, end - 1) + (if s[end - 1] == '0' then 1 else 0));
    assert ZeroCount(s, start, end) == ZeroCount(s, start, end - 1) + (if s[end - 1] == '0' then 1 else 0);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures result == DigitSum(s, 1, 7) + 9 * ZeroCount(s, 1, 7) + 1
// </vc-spec>
// <vc-code>
{
  var sum := 0;
  var zeros := 0;
  var i := 1;
  while i < 7
    invariant 1 <= i <= 7
    invariant sum == DigitSum(s, 1, i)
    invariant zeros == ZeroCount(s, 1, i)
    invariant forall k :: 1 <= k < 7 ==> '0' <= s[k] <= '9'
    decreases 7 - i
  {
    var ch := s[i];
    // establish bounds to satisfy lemmas' preconditions
    assert 1 <= i < 7;
    DigitSum_Append(s, 1, i + 1);
    ZeroCount_Append(s, 1, i + 1);
    sum := sum + (ch as int - '0' as int);
    if ch == '0' {
      zeros := zeros + 1;
    }
    i := i + 1;
  }
  result := sum + 9 * zeros + 1;
}
// </vc-code>

