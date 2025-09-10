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
lemma CountValidNumbersMatchesSet(numbers: seq<int>, k: int, upTo: int)
    requires 0 <= upTo <= |numbers|
    requires k >= 0
    requires forall i :: 0 <= i < |numbers| ==> numbers[i] >= 0
    ensures countValidNumbers(numbers, k, upTo) == |set i | 0 <= i < upTo && countLuckyDigits(numbers[i]) <= k|
    decreases upTo
{
    if upTo == 0 {
        assert countValidNumbers(numbers, k, 0) == 0;
        assert set i | 0 <= i < 0 && countLuckyDigits(numbers[i]) <= k == {};
    } else {
        CountValidNumbersMatchesSet(numbers, k, upTo - 1);
        var S_prev := set i | 0 <= i < upTo - 1 && countLuckyDigits(numbers[i]) <= k;
        var S := set i | 0 <= i < upTo && countLuckyDigits(numbers[i]) <= k;
        
        assert countValidNumbers(numbers, k, upTo - 1) == |S_prev|;
        
        if countLuckyDigits(numbers[upTo - 1]) <= k {
            assert countValidNumbers(numbers, k, upTo) == countValidNumbers(numbers, k, upTo - 1) + 1;
            assert S == S_prev + {upTo - 1};
            assert upTo - 1 !in S_prev;
            assert |S| == |S_prev| + 1;
        } else {
            assert countValidNumbers(numbers, k, upTo) == countValidNumbers(numbers, k, upTo - 1);
            assert S == S_prev;
            assert |S| == |S_prev|;
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
    CountValidNumbersMatchesSet(numbers, k, n);
    result := countValidNumbers(numbers, k, n);
}
// </vc-code>

