predicate ValidInput(K: int) {
    2 <= K <= 100
}

function CountOddNumbers(K: int): int
    requires K >= 1
{
    (K + 1) / 2
}

function CountEvenNumbers(K: int): int
    requires K >= 1
{
    K / 2
}

function ExpectedResult(K: int): int
    requires ValidInput(K)
{
    CountOddNumbers(K) * CountEvenNumbers(K)
}

predicate CorrectResult(K: int, result: int)
    requires ValidInput(K)
{
    result == ExpectedResult(K)
}

// <vc-helpers>
lemma CountOddNumbersCorrect(K: int)
    requires K >= 1
    ensures CountOddNumbers(K) == (K + 1) / 2
{
}

lemma CountEvenNumbersCorrect(K: int)
    requires K >= 1
    ensures CountEvenNumbers(K) == K / 2
{
}

lemma ExpectedResultCorrect(K: int)
    requires ValidInput(K)
    ensures ExpectedResult(K) == CountOddNumbers(K) * CountEvenNumbers(K)
{
}

lemma ResultNonNegative(K: int)
    requires ValidInput(K)
    ensures ExpectedResult(K) >= 0
{
    assert CountOddNumbers(K) >= 1;
    assert CountEvenNumbers(K) >= 1;
}
// </vc-helpers>

// <vc-spec>
method CountEvenOddPairs(K: int) returns (result: int)
    requires ValidInput(K)
    ensures CorrectResult(K, result)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    var oddCount := CountOddNumbers(K);
    var evenCount := CountEvenNumbers(K);
    result := oddCount * evenCount;
    
    ExpectedResultCorrect(K);
    ResultNonNegative(K);
}
// </vc-code>

