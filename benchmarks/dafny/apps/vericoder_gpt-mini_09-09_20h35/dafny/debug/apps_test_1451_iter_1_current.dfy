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
lemma CountValidNumbersSpec(numbers: seq<int>, k: int, upTo: int)
    requires 0 <= upTo <= |numbers|
    requires k >= 0
    requires forall i :: 0 <= i < |numbers| ==> numbers[i] >= 0
    ensures countValidNumbers(numbers, k, upTo) == |set i | 0 <= i < upTo && countLuckyDigits(numbers[i]) <= k|
    decreases upTo
{
    if upTo == 0 {
        // base case: both sides 0
        assert countValidNumbers(numbers, k, 0) == 0;
        assert |set i | 0 <= i < 0 && countLuckyDigits(numbers[i]) <= k| == 0;
    } else {
        CountValidNumbersSpec(numbers, k, upTo - 1);
        var prev := countValidNumbers(numbers, k, upTo - 1);
        assert prev == |set i | 0 <= i < upTo - 1 && countLuckyDigits(numbers[i]) <= k|;

        if countLuckyDigits(numbers[upTo - 1]) <= k {
            // by definition of countValidNumbers, it adds 1 in this case
            assert countValidNumbers(numbers, k, upTo) == prev + 1;
            // the set for upTo equals the previous set plus the last index
            assert (set i | 0 <= i < upTo && countLuckyDigits(numbers[i]) <= k) == (set i | 0 <= i < upTo - 1 && countLuckyDigits(numbers[i]) <= k) + {upTo - 1};
            assert |set i | 0 <= i < upTo && countLuckyDigits(numbers[i]) <= k| == prev + 1;
        } else {
            // by definition of countValidNumbers, it remains prev
            assert countValidNumbers(numbers, k, upTo) == prev;
            // the set for upTo equals the previous set (last index not included)
            assert (set i | 0 <= i < upTo && countLuckyDigits(numbers[i]) <= k) == (set i | 0 <= i < upTo - 1 && countLuckyDigits(numbers[i]) <= k);
            assert |set i | 0 <= i < upTo && countLuckyDigits(numbers[i]) <= k| == prev;
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
  result := countValidNumbers(numbers, k, n);
  CountValidNumbersSpec(numbers, k, n);
}
// </vc-code>

