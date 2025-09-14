function GenerateSquares(): seq<int>
    ensures forall i :: 0 <= i < |GenerateSquares()| ==> GenerateSquares()[i] > 0
{
    GenerateSquaresHelper(1, 44721)
}

function IsSubsequence(pattern: string, text: string): bool
{
    IsSubsequenceHelper(pattern, text, 0, 0)
}

function IntToString(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else IntToStringHelper(n)
}

// <vc-helpers>
function GenerateSquaresHelper(lo: int, hi: int): seq<int>
    requires lo >= 1
    ensures forall k :: 0 <= k < |GenerateSquaresHelper(lo, hi)| ==> GenerateSquaresHelper(lo, hi)[k] > 0
    decreases hi - lo + 1
{
    if lo > hi then [] else [lo*lo] + GenerateSquaresHelper(lo+1, hi)
}

function DigitString(d: int): string
    requires 0 <= d < 10
{
    if d == 0 then "0"
    else if d == 1 then "1"
    else if d == 2 then "2"
    else if d == 3 then "3"
    else if d == 4 then "4"
    else if d == 5 then "5"
    else if d == 6 then "6"
    else if d == 7 then "7"
    else if d == 8 then "8"
    else "9"
}

function IntToStringHelper(n: int): string
    requires n >= 0
    decreases n
{
    if n == 0 then "" else IntToStringHelper(n / 10) + DigitString(n % 10)
}

function IsSubsequenceHelper(pattern: string, text: string, i: int, j: int): bool
    requires 0 <= i <= |pattern|
    requires 0 <= j <= |text|
    decreases |text| - j
{
    if i == |pattern| then true
    else if j == |text| then false
    else if pattern[i] == text[j] then IsSubsequenceHelper(pattern, text, i+1, j+1)
    else IsSubsequenceHelper(pattern, text, i, j+1)
}

lemma {:auto} IntToStringHelper_nonempty(n: int)
    requires n > 0
    ensures |IntToStringHelper(n)| > 0
    decreases n
{
    if n / 10 != 0 {
        IntToStringHelper_nonempty(n / 10);
    } else {
        // n in 1..9, so IntToStringHelper(n) = "" + DigitString(n) has length > 0
    }
}

lemma {:auto} GenerateSquaresHelper_positive(lo: int, hi: int)
    requires lo >= 1
    ensures forall k :: 0 <= k < |GenerateSquaresHelper(lo, hi)| ==> GenerateSquaresHelper(lo, hi)[k] > 0
    decreases hi - lo + 1
{
    if lo > hi {
        // vacuously true
    } else {
        // head lo*lo is > 0 because lo >= 1
        GenerateSquaresHelper_positive(lo+1, hi);
    }
}

lemma {:auto} IsSubsequenceHelper_length(pattern: string, text: string, i: int, j: int)
    requires 0 <= i <= |pattern|
    requires 0 <= j <= |text|
    decreases |text| - j
    ensures IsSubsequenceHelper(pattern, text, i, j) ==> |pattern| - i <= |text| - j
{
    if i == |pattern| {
        // then |pattern|-i == 0 <= |text|-j
    } else if j == |text| {
        // then IsSubsequenceHelper(...) is false, implication holds
    } else {
        if pattern[i] == text[j] {
            IsSubsequenceHelper_length(pattern, text, i+1, j+1);
        } else {
            IsSubsequenceHelper_length(pattern, text, i, j+1);
        }
    }
}

lemma {:auto} IsSubsequence_length(pattern: string, text: string)
    ensures IsSubsequence(pattern, text) ==> |pattern| <= |text|
{
    IsSubsequenceHelper_length(pattern, text, 0, 0);
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires s[0] != '0' || |s| == 1
    ensures result == -1 || result >= 0
    ensures result == -1 ==> forall sq :: sq in GenerateSquares() ==> !IsSubsequence(IntToString(sq), s)
    ensures result >= 0 ==> exists sq :: sq in GenerateSquares() && IsSubsequence(IntToString(sq), s) && result == |s| - |IntToString(sq)|
    ensures result >= 0 ==> forall sq :: sq in GenerateSquares() && IsSubsequence(IntToString(sq), s) ==> |s| - |IntToString(sq)| >= result
// </vc-spec>
// <vc-code>
{
    var sqs := GenerateSquares();
    var bestlen := 0;
    var bestidx := 0;
    var i := 0;
    while i < |sqs|
        invariant 0 <= i <= |sqs|
        invariant 0 <= bestlen <= |s|
        invariant (bestlen == 0) ==> (forall idx :: 0 <= idx < i ==> !IsSubsequence(IntToString(sqs[idx]), s))
        invariant (bestlen != 0) ==> (0 <= bestidx < |sqs| && IsSubsequence(IntToString(sqs[bestidx]), s) && |IntToString(sqs[bestidx])| == bestlen)
        invariant forall idx :: 0 <= idx < i ==> (IsSubsequence(IntToString(sqs[idx]), s) ==> |IntToString(sqs[idx])| <= bestlen)
        decreases |sqs| - i
    {
        var cur := IntToString(sqs[i]);
        if IsSubsequence(cur, s) && |cur| > bestlen {
            IsSubsequence_length(cur, s);
            assert |cur| <= |s|;
            bestidx := i;
            bestlen := |cur|;
        }
        i := i + 1;
    }

    if bestlen == 0 {
        assert forall idx :: 0 <= idx < |sqs| ==> !IsSubsequence(IntToString(sqs[idx]), s);
        result := -1;
    } else {
        result := |s| - bestlen;
        assert 0 <= bestidx < |sqs|;
        assert IsSubsequence(IntToString(sqs[bestidx]), s);
        assert result == |s| - |IntToString(sqs[bestidx])|;
        assert forall idx :: 0 <= idx < |sqs| ==> (IsSubsequence(IntToString(sqs[idx]), s) ==> |IntToString(sqs[idx])| <= bestlen);
    }
}
// </vc-code>

