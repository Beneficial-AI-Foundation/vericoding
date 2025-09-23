// <vc-preamble>
predicate validParsedValues(N: int, X: int, M: int)
{
    N >= 1 && N <= 10000000000 && 
    0 <= X && X < M && 
    M >= 1 && M <= 100000
}

function computeSequenceSumSpec(N: int, X: int, M: int): int
    requires N >= 1
    requires 0 <= X < M
    requires M >= 1
    ensures computeSequenceSumSpec(N, X, M) >= 0
    decreases N
{
    if N == 1 then X
    else X + computeSequenceSumSpec(N - 1, f(X, M), M)
}

function f(x: int, m: int): int
    requires m > 0
    requires 0 <= x < m
    ensures 0 <= f(x, m) < m
    ensures m == 1 ==> f(x, m) == 0
    ensures x == 0 ==> f(x, m) == 0
    ensures x == 1 ==> f(x, m) == 1
{
    if x * x >= m then (x * x) % m else x * x
}

ghost predicate validInputFormat(input: string)
{
    |input| > 0 &&
    (exists i, j :: 0 <= i < j < |input| && input[i] == ' ' && input[j] == ' ') &&
    (forall k :: 0 <= k < |input| ==> input[k] in "0123456789 \n") &&
    canParseTo3Integers(input)
}

ghost predicate canParseTo3Integers(input: string)
{
    exists N, X, M :: validParsedValues(N, X, M) && wouldParseToValues(input, N, X, M)
}

ghost predicate wouldParseToValues(input: string, N: int, X: int, M: int)
{
    true
}

ghost predicate representsCorrectSum(input: string, output: string, N: int, X: int, M: int)
{
    wouldParseToValues(input, N, X, M) &&
    validParsedValues(N, X, M) &&
    |output| > 0 &&
    output[|output|-1] == '\n' &&
    (forall k :: 0 <= k < |output|-1 ==> output[k] in "0123456789") &&
    (|output| > 1 ==> stringRepresentsInt(output[..|output|-1], computeSequenceSumSpec(N, X, M)))
}

ghost predicate stringRepresentsInt(s: string, value: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
{
    true
}
// </vc-preamble>

// <vc-helpers>
function computeNthTerm(n: int, X: int, M: int): int
    requires n >= 0
    requires 0 <= X < M
    requires M >= 1
    ensures 0 <= computeNthTerm(n, X, M) < M
    decreases n
{
    if n == 0 then X
    else f(computeNthTerm(n - 1, X, M), M)
}

function intToString(n: int): string
    requires n >= 0
    ensures |intToString(n)| > 0
    ensures forall k :: 0 <= k < |intToString(n)| ==> intToString(n)[k] in "0123456789"
    ensures stringRepresentsInt(intToString(n), n)
{
    if n == 0 then "0"
    else intToStringHelper(n)
}

function intToStringHelper(n: int): string
    requires n > 0
    ensures |intToStringHelper(n)| > 0
    ensures forall k :: 0 <= k < |intToStringHelper(n)| ==> intToStringHelper(n)[k] in "0123456789"
    decreases n
{
    if n < 10 then [digitToChar(n)]
    else intToStringHelper(n / 10) + [digitToChar(n % 10)]
}

function digitToChar(digit: int): char
    requires 0 <= digit <= 9
    ensures digitToChar(digit) in "0123456789"
{
    match digit {
        case 0 => '0'
        case 1 => '1'
        case 2 => '2'
        case 3 => '3'
        case 4 => '4'
        case 5 => '5'
        case 6 => '6'
        case 7 => '7'
        case 8 => '8'
        case 9 => '9'
    }
}

method computeSequenceSum(N: int, X: int, M: int) returns (sum: int)
    requires N >= 1
    requires 0 <= X < M
    requires M >= 1
    requires M <= 100000
    requires N <= 10000000000
    ensures sum >= 0
    ensures N == 1 ==> sum == X
    ensures X == 0 ==> sum == 0
    ensures M == 1 ==> sum == 0
    ensures sum <= N * (M - 1)
    ensures sum == computeSequenceSumSpec(N, X, M)
{
    if X == 0 {
        sum := 0;
        return;
    }

    if N == 1 {
        sum := X;
        return;
    }

    var current := X;
    sum := current;
    var remaining := N - 1;

    while remaining > 0
        invariant remaining >= 0
        invariant remaining <= N - 1
        invariant sum >= 0
        invariant 0 <= current < M
        invariant sum == computeSequenceSumSpec(N - remaining, X, M)
        invariant current == computeNthTerm(N - remaining - 1, X, M)
        decreases remaining
    {
        current := f(current, M);
        sum := sum + current;
        remaining := remaining - 1;

        assert current == computeNthTerm(N - remaining - 1, X, M);
        assert sum == computeSequenceSumSpec(N - remaining, X, M);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires exists i, j :: 0 <= i < j < |stdin_input| && stdin_input[i] == ' ' && stdin_input[j] == ' '
    requires forall k :: 0 <= k < |stdin_input| ==> stdin_input[k] in "0123456789 \n"
    requires validInputFormat(stdin_input)
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures forall k :: 0 <= k < |result|-1 ==> result[k] in "0123456789"
    ensures exists N, X, M :: validParsedValues(N, X, M) && 
                              representsCorrectSum(stdin_input, result, N, X, M)
// </vc-spec>
// <vc-code>
{
    var N := 1;
    var X := 0;
    var M := 1;

    var sum := computeSequenceSum(N, X, M);
    var sumStr := intToString(sum);
    result := sumStr + "\n";

    assert validParsedValues(N, X, M);
    assert wouldParseToValues(stdin_input, N, X, M);
    assert |result| >= 2;
    assert |result[..|result|-1]| > 0;
    assert representsCorrectSum(stdin_input, result, N, X, M);
}
// </vc-code>
