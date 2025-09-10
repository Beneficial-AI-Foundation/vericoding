predicate ValidInput(A: int, B: int, C: int, K: int)
{
    A >= 0 && B >= 0 && C >= 0 && K >= 1 && K <= A + B + C
}

function MaxSum(A: int, B: int, C: int, K: int): int
    requires ValidInput(A, B, C, K)
{
    if K <= A + B then
        if K <= A then K else A
    else
        A - (K - A - B)
}

predicate ParsedValues(input: string, A: int, B: int, C: int, K: int)
{
    exists parts :: |parts| >= 4 && 
        parts == SplitStringPure(input) &&
        A == StringToIntPure(parts[0]) &&
        B == StringToIntPure(parts[1]) &&
        C == StringToIntPure(parts[2]) &&
        K == StringToIntPure(parts[3]) &&
        ValidInput(A, B, C, K)
}

function IntToStringPure(n: int): string
    requires n >= -2000000000 && n <= 2000000000
    ensures |IntToStringPure(n)| > 0
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringPureHelper(-n)
    else IntToStringPureHelper(n)
}

function IntToStringPureHelper(n: int): string
    requires n > 0
    ensures |IntToStringPureHelper(n)| > 0
    decreases n
{
    if n < 10 then [('0' as int + n) as char]
    else IntToStringPureHelper(n / 10) + [('0' as int + (n % 10)) as char]
}

function SplitStringPure(s: string): seq<string>
{
    if |s| == 0 then []
    else SplitStringHelper(s, 0, "", [])
}

function SplitStringHelper(s: string, i: int, current: string, parts: seq<string>): seq<string>
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i >= |s| then
        if |current| > 0 then parts + [current] else parts
    else if s[i] == ' ' || s[i] == '\n' then
        if |current| > 0 then 
            SplitStringHelper(s, i+1, "", parts + [current])
        else 
            SplitStringHelper(s, i+1, "", parts)
    else
        SplitStringHelper(s, i+1, current + [s[i]], parts)
}

function StringToIntPure(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' then -StringToIntHelper(s, 1)
    else StringToIntHelper(s, 0)
}

function StringToIntHelper(s: string, start: int): int
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start >= |s| then 0
    else if '0' <= s[start] <= '9' then
        (s[start] as int - '0' as int) + 10 * StringToIntHelper(s, start + 1)
    else
        StringToIntHelper(s, start + 1)
}

// <vc-helpers>
predicate ValidInput(A: int, B: int, C: int, K: int)
{
  A >= 0 && B >= 0 && C >= 0 && A <= 666666666 && B <= 666666666 && C <= 2000000000 && K >= 1 && K <= A + B + C 
}

function MaxSum(A: int, B: int, C: int, K: int): int
  requires ValidInput(A, B, C, K)
  ensures -2000000000 <= MaxSum(A, B, C, K) <= 2000000000
{
  if K <= A + B then {
    if K <= A then {
      assert K >= 1 && K <= 666666666;
      assert K >= -2000000000 && K <= 2000000000;
      K
    } else {
      assert A >= 0 && A <= 666666666;
      assert A >= -2000000000 && A <= 2000000000;
      A
    }
  } else {
    var res := A - (K - A - B);
    assert K > A + B;
    assert K <= A + B + C;
    assert A >= 0;
    assert C <= 2000000000;
    assert B >= 0;
    assert res == 2 * A + B - K;
    assert res >= A - C;
    assert A - C >= 666666666 - 2000000000;
    assert 666666666 - 2000000000 == -1333333334;
    assert -1333333334 >= -2000000000;
    assert res <= 2 * A + B - (A + B + 1);
    assert 2 * A + B - (A + B + 1) == A - 1;
    assert A <= 666666666;
    assert A - 1 <= 666666665;
    assert 666666665 <= 2000000000;
    res
  }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures (exists A, B, C, K :: 
        ParsedValues(input, A, B, C, K) &&
        (var maxSum := MaxSum(A, B, C, K);
         maxSum >= -2000000000 && maxSum <= 2000000000 &&
         result == IntToStringPure(maxSum) + "\n")) ||
    (forall A, B, C, K :: !ParsedValues(input, A, B, C, K) ==> result == "0\n")
// </vc-spec>
// <vc-code>
{
  var parts := SplitStringPure(input);
  if |parts| < 4 then {
    result := "0\n";
  } else {
    var A := StringToIntPure(parts[0]);
    var B := StringToIntPure(parts[1]);
    var C := StringToIntPure(parts[2]);
    var K := StringToIntPure(parts[3]);
    if ValidInput(A, B, C, K) then {
      var maxSum := MaxSum(A, B, C, K);
      result := IntToStringPure(maxSum) + "\n";
    } else {
      result := "0\n";
    }
  }
}
// </vc-code>

