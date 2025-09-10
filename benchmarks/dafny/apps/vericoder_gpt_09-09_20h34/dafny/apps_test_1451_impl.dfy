predicate ValidInput(n: int, k: int, numbers: seq<int>)
{
    n >= 1 && k >= 0 && |numbers| == n && forall i :: 0 <= i < |numbers| ==> numbers[i] > 0
}

function countLuckyDigits(num: int): int
    requires num >= 0
    ensures countLuckyDigits(num) >= 0
    ensures num == 0 ==> countLuckyDigits(num) == 0
    ensures num > 0 ==> countLuckyDigits(num) == (if (num % 10 == 4 || num % 10 == 7) then 1 else 0) + countLuckyDigits(num / 10)
{
    if num == 0 then 0
    else
        var digit := num % 10;
        var rest := num / 10;
        var digitCount := if digit == 4 || digit == 7 then 1 else 0;
        digitCount + countLuckyDigits(rest)
}

function countValidNumbers(numbers: seq<int>, k: int, upTo: int): int
    requires 0 <= upTo <= |numbers|
    requires k >= 0
    requires forall i :: 0 <= i < |numbers| ==> numbers[i] >= 0
    ensures 0 <= countValidNumbers(numbers, k, upTo) <= upTo
{
    if upTo == 0 then 0
    else 
        var prevCount := countValidNumbers(numbers, k, upTo - 1);
        if countLuckyDigits(numbers[upTo - 1]) <= k then prevCount + 1 else prevCount
}

// <vc-helpers>
// no helper updates needed
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, numbers: seq<int>) returns (result: int)
    requires ValidInput(n, k, numbers)
    ensures 0 <= result <= n
    ensures result == |set i | 0 <= i < |numbers| && countLuckyDigits(numbers[i]) <= k|
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := 0;
  ghost var S: set<int> := {};
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant 0 <= result <= i
    invariant result == |S|
    invariant S == set j | 0 <= j < i && countLuckyDigits(numbers[j]) <= k
    decreases |numbers| - i
  {
    if countLuckyDigits(numbers[i]) <= k {
      assert i !in S;
      ghost var S0 := S;
      ghost var r0 := result;
      assert i !in S0;
      S := S + {i};
      result := result + 1;
      assert S == S0 + {i};
      assert |S| == |S0| + 1;
      assert r0 == |S0|;
      assert result == |S|;
    }
    i := i + 1;
  }
  assert i == |numbers|;
  assert S == set j | 0 <= j < |numbers| && countLuckyDigits(numbers[j]) <= k;
  assert result == |set j | 0 <= j < |numbers| && countLuckyDigits(numbers[j]) <= k|;
}
// </vc-code>

