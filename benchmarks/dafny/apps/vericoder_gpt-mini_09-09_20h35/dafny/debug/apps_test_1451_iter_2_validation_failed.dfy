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
        // Inductive hypothesis
        CountValidNumbersSpec(numbers, k, upTo - 1);
        var prev := countValidNumbers(numbers, k, upTo - 1);
        assert prev == |set i | 0 <= i < upTo - 1 && countLuckyDigits(numbers[i]) <= k|;

        var Sprev := set i | 0 <= i < upTo - 1 && countLuckyDigits(numbers[i]) <= k;
        var Sup := set i | 0 <= i < upTo && countLuckyDigits(numbers[i]) <= k;

        if countLuckyDigits(numbers[upTo - 1]) <= k {
            // countValidNumbers adds 1 in this case
            assert countValidNumbers(numbers, k, upTo) == prev + 1;

            // Show Sup == Sprev + {upTo - 1}

            // Sup subset Sprev + {upTo-1}
            assert forall j :: 0 <= j < upTo && countLuckyDigits(numbers[j]) <= k ==> j in Sprev + {upTo - 1}
            {
                fix j;
                assume H: 0 <= j < upTo && countLuckyDigits(numbers[j]) <= k;
                if j == upTo - 1 {
                    assert j in {upTo - 1};
                    assert j in Sprev + {upTo - 1};
                } else {
                    // j < upTo and j != upTo-1 implies j < upTo-1
                    assert j < upTo - 1;
                    assert 0 <= j < upTo - 1;
                    assert countLuckyDigits(numbers[j]) <= k;
                    assert j in Sprev;
                    assert j in Sprev + {upTo - 1};
                }
            }

            // Sprev + {upTo-1} subset Sup
            assert forall j :: j in Sprev + {upTo - 1} ==> 0 <= j < upTo && countLuckyDigits(numbers[j]) <= k
            {
                fix j;
                assume H: j in Sprev + {upTo - 1};
                if j in Sprev {
                    assert 0 <= j < upTo - 1;
                    assert countLuckyDigits(numbers[j]) <= k;
                    assert 0 <= j < upTo;
                } else {
                    // j in {upTo - 1}
                    assert j == upTo - 1;
                    assert 0 <= j < upTo;
                    assert countLuckyDigits(numbers[j]) <= k;
                }
            }

            // From the two forall assertions we get set equality
            assert Sup == Sprev + {upTo - 1};

            // Now relate cardinalities
            assert |Sup| == |Sprev + {upTo - 1}|;
            assert |Sprev| == prev;
            // Since upTo-1 is not in Sprev (elements of Sprev are < upTo-1), the union adds exactly one element
            assert upTo - 1 !in Sprev;
            // Hence cardinality increases by 1
            assert |Sprev + {upTo - 1}| == |Sprev| + 1;
            assert |Sup| == prev + 1;
        } else {
            // countValidNumbers remains prev
            assert countValidNumbers(numbers, k, upTo) == prev;

            // Show Sup == Sprev (last index not included)
            assert forall j :: 0 <= j < upTo && countLuckyDigits(numbers[j]) <= k ==> j in Sprev
            {
                fix j;
                assume H: 0 <= j < upTo && countLuckyDigits(numbers[j]) <= k;
                // If j were upTo-1, then countLuckyDigits(numbers[upTo-1]) <= k would hold, contradicting branch
                if j == upTo - 1 {
                    // derive contradiction to eliminate this case
                    assert countLuckyDigits(numbers[upTo - 1]) <= k by { reveal countLuckyDigits; }
                    // But we're in the branch where that's false, so this branch cannot happen.
                } else {
                    assert j < upTo - 1;
                    assert 0 <= j < upTo - 1;
                    assert countLuckyDigits(numbers[j]) <= k;
                    assert j in Sprev;
                }
            }

            assert forall j :: j in Sprev ==> 0 <= j < upTo && countLuckyDigits(numbers[j]) <= k
            {
                fix j;
                assume H: j in Sprev;
                assert 0 <= j < upTo - 1;
                assert countLuckyDigits(numbers[j]) <= k;
                assert 0 <= j < upTo;
            }

            assert Sup == Sprev;
            assert |Sup| == |Sprev|;
            assert |Sup| == prev;
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

