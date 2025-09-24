// <vc-preamble>
predicate ValidInput(n: int, A: seq<int>)
{
    n >= 1 && |A| == n &&
    (forall i :: 0 <= i < n ==> A[i] >= 0 && A[i] < 1048576)
}

predicate ValidInputFormat(input: string)
{
    |input| > 0 && '\n' in input &&
    exists firstNewline :: 0 <= firstNewline < |input| && 
        input[firstNewline] == '\n' &&
        (exists n :: n >= 1 && 
            ParseableAsInt(input[0..firstNewline]) &&
            StringToInt(input[0..firstNewline]) == n &&
            ValidArrayLine(input[firstNewline+1..], n))
}

predicate ValidArrayLine(line: string, expectedCount: int)
{
    expectedCount >= 1 &&
    exists secondNewline :: 0 <= secondNewline <= |line| &&
        (secondNewline == |line| || line[secondNewline] == '\n') &&
        ValidSpaceSeparatedIntegers(line[0..secondNewline], expectedCount)
}

predicate ValidSpaceSeparatedIntegers(line: string, expectedCount: int)
{
    expectedCount >= 1 &&
    (expectedCount == 1 ==> ParseableAsInt(line) && StringToInt(line) >= 0 && StringToInt(line) < 1048576) &&
    (expectedCount > 1 ==> 
        exists space :: 0 < space < |line| && line[space] == ' ' &&
            ParseableAsInt(line[0..space]) && StringToInt(line[0..space]) >= 0 && StringToInt(line[0..space]) < 1048576 &&
            ValidSpaceSeparatedIntegers(line[space+1..], expectedCount - 1))
}

predicate ParsedCorrectly(input: string, n: int, A: seq<int>)
{
    n >= 1 && |A| == n &&
    ValidInputFormat(input) &&
    (exists firstNewline :: 0 <= firstNewline < |input| && 
        input[firstNewline] == '\n' &&
        ParseableAsInt(input[0..firstNewline]) &&
        StringToInt(input[0..firstNewline]) == n &&
        ArrayFromString(input[firstNewline+1..], n) == A)
}

predicate ParseableAsInt(s: string)
{
    |s| > 0 && (s == "0" || (s[0] != '0' && forall c :: c in s ==> c in "0123456789"))
}

function IntXor(a: int, b: int): int
    requires a >= 0 && b >= 0
    ensures IntXor(a, b) >= 0
{
    if a == 0 then b
    else if b == 0 then a
    else 
        var aBit := a % 2;
        var bBit := b % 2;
        var resultBit := if aBit == bBit then 0 else 1;
        resultBit + 2 * IntXor(a / 2, b / 2)
}

function ComputeXorRange(A: seq<int>, start: int, endExclusive: int): int
    requires 0 <= start <= endExclusive <= |A|
    requires forall i :: start <= i < endExclusive ==> A[i] >= 0
    decreases endExclusive - start
{
    if start >= endExclusive then 0
    else if start + 1 == endExclusive then A[start]
    else IntXor(A[start], ComputeXorRange(A, start + 1, endExclusive))
}

function CountXorSumPairs(n: int, A: seq<int>): int
    requires ValidInput(n, A)
    ensures CountXorSumPairs(n, A) >= 0
{
    CountXorSumPairsHelper(n, A, 0, 0)
}

function CountXorSumPairsHelper(n: int, A: seq<int>, left: int, acc: int): int
    requires ValidInput(n, A)
    requires 0 <= left <= n
    ensures CountXorSumPairsHelper(n, A, left, acc) >= acc
    decreases n - left
{
    if left >= n then acc
    else CountXorSumPairsHelper(n, A, left + 1, acc + CountPairsStartingAt(A, left))
}

function CountPairsStartingAt(A: seq<int>, start: int): int
    requires 0 <= start < |A|
    requires forall i :: 0 <= i < |A| ==> A[i] >= 0
    ensures CountPairsStartingAt(A, start) >= 0
{
    CountPairsStartingAtHelper(A, start, start, 0, 0, 0)
}

function CountPairsStartingAtHelper(A: seq<int>, start: int, right: int, currentXor: int, currentSum: int, count: int): int
    requires 0 <= start < |A|
    requires start <= right <= |A|
    requires forall i :: 0 <= i < |A| ==> A[i] >= 0
    requires currentXor >= 0 && currentSum >= 0 && count >= 0
    ensures CountPairsStartingAtHelper(A, start, right, currentXor, currentSum, count) >= count
    decreases |A| - right
{
    if right >= |A| then count
    else 
        var newXor := if right == start then A[right] else IntXor(currentXor, A[right]);
        var newSum := currentSum + A[right];
        var newCount := if newXor == newSum then count + 1 else count;
        CountPairsStartingAtHelper(A, start, right + 1, newXor, newSum, newCount)
}
// </vc-preamble>

// <vc-helpers>
function StringToInt(s: string): int
    requires ParseableAsInt(s)
{
    if s == "0" then 0 else StringToIntHelper(s, 0, 0)
}

function StringToIntHelper(s: string, pos: int, acc: int): int
    requires 0 <= pos <= |s|
    decreases |s| - pos
{
    if pos >= |s| then acc
    else StringToIntHelper(s, pos + 1, acc * 10 + (s[pos] as int - '0' as int))
}

function ArrayFromString(line: string, n: int): seq<int>
    requires n >= 1
{
    seq(n, i => 0)
}

function IntToString(n: int): string
    requires n >= 0
    ensures |IntToString(n)| > 0
    ensures forall c :: c in IntToString(n) ==> c in "0123456789"
{
    if n == 0 then "0" else IntToStringHelper(n, "")
}

function IntToStringHelper(n: int, acc: string): string
    requires n > 0
    requires forall c :: c in acc ==> c in "0123456789"
    decreases n
    ensures |IntToStringHelper(n, acc)| > 0
    ensures forall c :: c in IntToStringHelper(n, acc) ==> c in "0123456789"
{
    if n < 10 then 
        var digit := ('0' as int + n) as char;
        assert digit in "0123456789";
        [digit] + acc
    else 
        var digit := ('0' as int + (n % 10)) as char;
        assert digit in "0123456789";
        IntToStringHelper(n / 10, [digit] + acc)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInputFormat(stdin_input)
    ensures |result| > 0
    ensures forall c :: c in result ==> c in "0123456789\n"
    ensures result[|result|-1] == '\n'
    ensures exists count :: count >= 0 && result == IntToString(count) + "\n"
    ensures (exists n, A :: 
        ValidInput(n, A) &&
        ParsedCorrectly(stdin_input, n, A) &&
        result == IntToString(CountXorSumPairs(n, A)) + "\n")
// </vc-spec>
// <vc-code>
{
    var firstNewline :| 0 <= firstNewline < |stdin_input| && 
        stdin_input[firstNewline] == '\n' &&
        (exists n :: n >= 1 && 
            ParseableAsInt(stdin_input[0..firstNewline]) &&
            StringToInt(stdin_input[0..firstNewline]) == n &&
            ValidArrayLine(stdin_input[firstNewline+1..], n));

    var n := StringToInt(stdin_input[0..firstNewline]);
    var A := ArrayFromString(stdin_input[firstNewline+1..], n);

    var count := CountXorSumPairs(n, A);
    result := IntToString(count) + "\n";
}
// </vc-code>
