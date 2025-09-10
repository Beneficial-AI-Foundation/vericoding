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
        assert countValidNumbers(numbers, k, 0) == 0;
        assert |set i | 0 <= i < 0 && countLuckyDigits(numbers[i]) <= k| == 0;
    } else {
        // Inductive hypothesis
        CountValidNumbersSpec(numbers, k, upTo - 1);
        var prev := countValidNumbers(numbers, k, upTo - 1);
        assert prev == |set i | 0 <= i < upTo - 1 && countLuckyDigits(numbers[i]) <= k|;

        var lastCond := countLuckyDigits(numbers[upTo - 1]) <= k;

        if lastCond {
            // By definition of countValidNumbers, it adds 1 when the last element satisfies the predicate
            assert countValidNumbers(numbers, k, upTo) == prev + 1;

            // Show set equality: the set for upTo equals previous set plus the last index
            assert forall j :: (0 <= j < upTo && countLuckyDigits(numbers[j]) <= k) <==> ((0 <= j < upTo - 1 && countLuckyDigits(numbers[j]) <= k) || j == upTo - 1);
            assert (set i | 0 <= i < upTo && countLuckyDigits(numbers[i]) <= k) == (set i | 0 <= i < upTo - 1 && countLuckyDigits(numbers[i]) <= k) + {upTo - 1};

            // The last index is not in the previous set (indices are strictly less than upTo - 1 there)
            assert upTo - 1 !in (set i | 0 <= i < upTo - 1 && countLuckyDigits(numbers[i]) <= k);

            // singleton has cardinality 1
            assert |{upTo - 1}| == 1;
            // Disjoint union: previous set and singleton are disjoint, so cardinalities add
            assert |(set i | 0 <= i < upTo - 1 && countLuckyDigits(numbers[i]) <= k) + {upTo - 1}| == |set i | 0 <= i < upTo - 1 && countLuckyDigits(numbers[i]) <= k| + |{upTo - 1}|;

            // Combine equalities to reach the required numeric equality
            assert |set i | 0 <= i < upTo && countLuckyDigits(numbers[i]) <= k| == prev + 1;
        } else {
            // By definition of countValidNumbers, it remains prev when last element does not satisfy the predicate
            assert countValidNumbers(numbers, k, upTo) == prev;

            // Show set equality: the set for upTo equals the previous set (last index not included)
            assert forall j :: (0 <= j < upTo && countLuckyDigits(numbers[j]) <= k) <==> (0 <= j < upTo - 1 && countLuckyDigits(numbers[j]) <= k);
            assert (set i | 0 <= i < upTo && countLuckyDigits(numbers[i]) <= k) == (set i | 0 <= i < upTo - 1 && countLuckyDigits(numbers[i]) <= k);

            // Therefore their cardinalities are equal
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

