predicate ValidInput(y: int)
{
    1000 <= y <= 9000
}

function HasDistinctDigits(n: int): bool
{
    var digits := NumberToDigits(n);
    AllDistinct(digits)
}

function NumberToDigits(n: int): seq<int>
{
    if n == 0 then [0]
    else if n > 0 then NumberToDigitsHelper(n, [])
    else NumberToDigitsHelper(-n, [])
}

function NumberToDigitsHelper(n: int, acc: seq<int>): seq<int>
requires n >= 0
decreases n
{
    if n == 0 then acc
    else NumberToDigitsHelper(n / 10, [n % 10] + acc)
}

predicate AllDistinct(digits: seq<int>)
{
    forall i, j :: 0 <= i < j < |digits| ==> digits[i] != digits[j]
}

// <vc-helpers>
lemma DistinctDigitsExist(y: int)
    requires ValidInput(y)
    ensures exists n :: n > y && n < 10000 && HasDistinctDigits(n)
{
    // 9876 has distinct digits and is greater than any y in range [1000, 9000]
    assert HasDistinctDigits(9876);
    assert 9876 > y;
    assert 9876 < 10000;
}

lemma VerifyMinimality(y: int, result: int)
    requires ValidInput(y)
    requires result > y
    requires HasDistinctDigits(result)
    requires forall n :: y < n < result ==> !HasDistinctDigits(n)
    ensures forall n :: y < n < result ==> !HasDistinctDigits(n)
{
    // This lemma just restates the requirement for clarity
}

lemma BoundExists(y: int) returns (bound: int)
    requires ValidInput(y)
    ensures bound > y && bound < 10000 && HasDistinctDigits(bound)
{
    DistinctDigitsExist(y);
    var n :| n > y && n < 10000 && HasDistinctDigits(n);
    bound := n;
}
// </vc-helpers>

// <vc-spec>
method solve(y: int) returns (result: int)
requires ValidInput(y)
ensures result > y
ensures HasDistinctDigits(result)
ensures forall n :: y < n < result ==> !HasDistinctDigits(n)
// </vc-spec>
// <vc-code>
{
    var bound := BoundExists(y);
    var candidate := y + 1;
    
    // Find the first number with distinct digits
    while !HasDistinctDigits(candidate)
        invariant candidate > y
        invariant candidate <= bound
        invariant forall n :: y < n < candidate ==> !HasDistinctDigits(n)
        decreases bound - candidate
    {
        candidate := candidate + 1;
    }
    
    result := candidate;
}
// </vc-code>

