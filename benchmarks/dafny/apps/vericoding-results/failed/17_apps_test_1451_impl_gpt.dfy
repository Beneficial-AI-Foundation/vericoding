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
lemma NonNegNumbersFromValidInput(n: int, k: int, numbers: seq<int>)
  requires ValidInput(n, k, numbers)
  ensures forall i :: 0 <= i < |numbers| ==> numbers[i] >= 0
{
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
  var c := 0;
  var i := 0;
  NonNegNumbersFromValidInput(n, k, numbers);
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant 0 <= c <= i
    invariant forall j :: 0 <= j < |numbers| ==> numbers[j] >= 0
    invariant c == |set j | 0 <= j < i && countLuckyDigits(numbers[j]) <= k|
    decreases |numbers| - i
  {
    assert 0 <= i < |numbers|;
    assert numbers[i] >= 0;
    if countLuckyDigits(numbers[i]) <= k {
      c := c + 1;
      assert c == |set j | 0 <= j < i + 1 && countLuckyDigits(numbers[j]) <= k|;
    } else {
      assert c == |set j | 0 <= j < i + 1 && countLuckyDigits(numbers[j]) <= k|;
    }
    i := i + 1;
  }
  result := c;
}
// </vc-code>

