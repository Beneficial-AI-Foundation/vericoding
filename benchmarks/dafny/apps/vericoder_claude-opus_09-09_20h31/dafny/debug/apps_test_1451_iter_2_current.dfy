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
{
    if upTo == 0 {
        var emptySet := set i | 0 <= i < 0 && countLuckyDigits(numbers[i]) <= k;
        assert emptySet == {};
    } else {
        CountValidNumbersMatchesSet(numbers, k, upTo - 1);
        var prevSet := set i | 0 <= i < upTo - 1 && countLuckyDigits(numbers[i]) <= k;
        var currSet := set i | 0 <= i < upTo && countLuckyDigits(numbers[i]) <= k;
        
        if countLuckyDigits(numbers[upTo - 1]) <= k {
            assert currSet == prevSet + {upTo - 1};
            assert |currSet| == |prevSet| + 1;
        } else {
            assert currSet == prevSet;
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
    var count := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant 0 <= count <= i
        invariant count == countValidNumbers(numbers, k, i)
        invariant count == |set j | 0 <= j < i && countLuckyDigits(numbers[j]) <= k|
    {
        var luckyCount := countLuckyDigits(numbers[i]);
        if luckyCount <= k {
            count := count + 1;
        }
        
        // Prove loop invariant maintenance
        var oldSet := set j | 0 <= j < i && countLuckyDigits(numbers[j]) <= k;
        var newSet := set j | 0 <= j < i + 1 && countLuckyDigits(numbers[j]) <= k;
        
        if luckyCount <= k {
            assert newSet == oldSet + {i};
        } else {
            assert newSet == oldSet;
        }
        
        CountValidNumbersMatchesSet(numbers, k, i + 1);
        i := i + 1;
    }
    
    assert i == n;
    CountValidNumbersMatchesSet(numbers, k, n);
    result := count;
}
// </vc-code>

