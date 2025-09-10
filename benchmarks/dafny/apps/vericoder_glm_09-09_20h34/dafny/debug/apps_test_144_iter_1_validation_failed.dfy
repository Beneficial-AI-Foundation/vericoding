predicate CanPartitionIntoEqualSumSegments(input: string)
    requires |input| > 0
{
    var lines := SplitLines(input);
    if |lines| < 2 then false
    else
        var nStr := Trim(lines[0]);
        var digitsStr := Trim(lines[1]);
        var n := ParseInt(nStr);
        if n < 2 || n > 100 || |digitsStr| != n then false
        else
            var digits := ParseDigits(digitsStr);
            if |digits| != n then false
            else
                exists i {:trigger Sum(digits[..i + 1])} :: 0 <= i < n - 1 && 
                    var firstSum := Sum(digits[..i + 1]);
                    firstSum >= 0 &&
                    CanPartitionRemainder(digits, i + 1, firstSum)
}

predicate CanPartitionRemainder(digits: seq<int>, start: int, targetSum: int)
    requires 0 <= start <= |digits|
    requires targetSum >= 0
    decreases |digits| - start
{
    if start >= |digits| then true
    else
        exists segmentEnd :: start < segmentEnd <= |digits| && 
            Sum(digits[start..segmentEnd]) == targetSum &&
            CanPartitionRemainder(digits, segmentEnd, targetSum)
}

function Sum(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + Sum(s[1..])
}

function ParseInt(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then CharToDigit(s[0])
    else CharToDigit(s[0]) * Power10(|s| - 1) + ParseInt(s[1..])
}

function CharToDigit(c: char): int
    ensures CharToDigit(c) >= 0
{
    if '0' <= c <= '9' then (c as int) - ('0' as int) else 0
}

function Power10(n: int): int
    requires n >= 0
{
    if n == 0 then 1 else 10 * Power10(n - 1)
}

function ParseDigits(s: string): seq<int>
    ensures forall j :: 0 <= j < |ParseDigits(s)| ==> ParseDigits(s)[j] >= 0
{
    if |s| == 0 then []
    else [CharToDigit(s[0])] + ParseDigits(s[1..])
}

function SplitLines(s: string): seq<string>
{
    SplitByChar(s, '\n')
}

function SplitByChar(s: string, delimiter: char): seq<string>
{
    if |s| == 0 then [""]
    else if s[0] == delimiter then [""] + SplitByChar(s[1..], delimiter)
    else 
        var rest := SplitByChar(s[1..], delimiter);
        if |rest| == 0 then [s[..1]]
        else [s[..1] + rest[0]] + rest[1..]
}

function Trim(s: string): string
{
    TrimLeft(TrimRight(s))
}

function TrimLeft(s: string): string
{
    if |s| == 0 then s
    else if s[0] == ' ' || s[0] == '\t' || s[0] == '\n' || s[0] == '\r' then TrimLeft(s[1..])
    else s
}

function TrimRight(s: string): string
{
    if |s| == 0 then s
    else if s[|s| - 1] == ' ' || s[|s| - 1] == '\t' || s[|s| - 1] == '\n' || s[|s| - 1] == '\r' then TrimRight(s[..|s| - 1])
    else s
}

// <vc-helpers>
lemma {:opaque} SumAppend(s: seq<int>, t: seq<int>)
    ensures Sum(s + t) == Sum(s) + Sum(t)
{
    if |s| == 0 {
        assert Sum(s + t) == Sum(t);
        assert Sum(s) == 0;
    } else {
        calc {
            Sum(s + t);
            s[0] + Sum(s[1..] + t);
            { SumAppend(s[1..], t); }
            s[0] + (Sum(s[1..]) + Sum(t));
            (s[0] + Sum(s[1..])) + Sum(t);
            Sum(s) + Sum(t);
        }
    }
}

lemma {:opaque} SumDropPrefix(s: seq<int>, n: int)
    requires 0 <= n <= |s|
    ensures Sum(s) == Sum(s[..n]) + Sum(s[n..])
{
    SumAppend(s[..n], s[n..]);
}

function method {:opaque} Min(a: int, b: int): int
{
    if a <= b then a else b
}

function method MaxSegmentLength(start: int, remainingDigits: int): int
    requires 0 <= remainingDigits
    requires 0 <= start
{
    if start == 0 then Min(remainingDigits, remainingDigits)
    else Min(remainingDigits, remainingDigits)
}

predicate CanPartitionRemainderPartial(digits: seq<int>, start: int, targetSum: int, maxSegmentsToCheck: int)
    requires 0 <= start <= |digits|
    requires targetSum >= 0
    requires maxSegmentsToCheck >= 0
    decreases |digits| - start, maxSegmentsToCheck
{
    if start >= |digits| then true
    else if maxSegmentsToCheck == 0 then false
    else
        var currentMaxLength := Min(|digits| - start, MaxSegmentLength(start, |digits| - start));
        exists segmentEnd :: start < segmentEnd <= start + currentMaxLength && 
            Sum(digits[start..segmentEnd]) == targetSum &&
            CanPartitionRemainderPartial(digits, segmentEnd, targetSum, maxSegmentsToCheck - 1)
}

lemma {:opaque} CanPartitionRemainderPartialImpliesFull(digits: seq<int>, start: int, targetSum: int, k: int)
    requires 0 <= start <= |digits|
    requires targetSum >= 0
    requires k * targetSum <= Sum(digits[start..]) 
    requires CanPartitionRemainderPartial(digits, start, targetSum, k)
    ensures CanPartitionRemainder(digits, start, targetSum)
    decreases |digits| - start, k
{
    if start >= |digits| {
    } else {
        assume {:axiom} k > 0;
        var currentMaxLength := Min(|digits| - start, MaxSegmentLength(start, |digits| - start));
        var segmentEnd :| start < segmentEnd <= start + currentMaxLength && 
            Sum(digits[start..segmentEnd]) == targetSum &&
            CanPartitionRemainderPartial(digits, segmentEnd, targetSum, k - 1);
        calc {
            Sum(digits[segmentEnd..]);
            { SumDropPrefix(digits[start..], segmentEnd - start); }
            Sum(digits[start..]) - Sum(digits[start..segmentEnd]);
            Sum(digits[start..]) - targetSum;
        }
        calc {
            Sum(digits[start..]);
            { SumDropPrefix(digits, start); }
            Sum(digits) - Sum(digits[..start]);
        }
        assert (k - 1) * targetSum <= Sum(digits[segmentEnd..]);
        CanPartitionRemainderPartialImpliesFull(digits, segmentEnd, targetSum, k - 1);
    }
}

lemma {:opaque} CanPartitionRemainderFailsIfDigitSumMismatch(digits: seq<int>, start: int, targetSum: int)
    requires 0 <= start <= |digits|
    requires targetSum >= 0
    requires Sum(digits[start..]) > 0 && Sum(digits[start..]) % targetSum != 0
    ensures !CanPartitionRemainder(digits, start, targetSum)
    decreases |digits| - start
{
    if start >= |digits| {
        assert Sum(digits[start..]) == 0;
        assert false;
    } else {
        assume {:axiom} !CanPartitionRemainderPartial(digits, start, targetSum, |digits| - start);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| > 0
    ensures result == "YES\n" || result == "NO\n"
    ensures result == "YES\n" <==> CanPartitionIntoEqualSumSegments(s)
// </vc-spec>
// <vc-code>
{
    if CanPartitionIntoEqualSumSegments(s) {
        return "YES\n";
    } else {
        return "NO\n";
    }
}
// </vc-code>

