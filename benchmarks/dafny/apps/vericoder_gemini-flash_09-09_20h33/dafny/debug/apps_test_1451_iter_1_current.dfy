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
lemma CountValidNumbersIsCorrect(numbers: seq<int>, k: int, i: int)
  requires 0 <= i <= |numbers|
  requires k >= 0
  requires forall j :: 0 <= j < |numbers| ==> numbers[j] >= 0
  ensures countValidNumbers(numbers, k, i) == |set j | 0 <= j < i && countLuckyDigits(numbers[j]) <= k|
{
  if i == 0 {
    assert countValidNumbers(numbers, k, 0) == 0;
    assert |set j | 0 <= j < 0 && countLuckyDigits(numbers[j]) <= k| == 0;
  } else {
    calc {
      countValidNumbers(numbers, k, i);
      (if countLuckyDigits(numbers[i - 1]) <= k then 1 else 0) + countValidNumbers(numbers, k, i - 1);
        {
          CountValidNumbersIsCorrect(numbers, k, i - 1);
        }
      (if countLuckyDigits(numbers[i - 1]) <= k then 1 else 0) + |set j | 0 <= j < i - 1 && countLuckyDigits(numbers[j]) <= k|;
      |set j | 0 <= j < i && countLuckyDigits(numbers[j]) <= k|;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, numbers: seq<int>) returns (result: int)
    requires ValidInput(n, k, numbers)
    ensures 0 <= result <= n
    ensures result == |set i | 0 <= i < |numbers| && countLuckyDigits(numbers[i]) <= k|
// </vc-spec>
// <vc-code>
{
  assert forall i :: 0 <= i < |numbers| ==> numbers[i] >= 0; // Follows from ValidInput
  CountValidNumbersIsCorrect(numbers, k, n);
  return countValidNumbers(numbers, k, n);
}
// </vc-code>

