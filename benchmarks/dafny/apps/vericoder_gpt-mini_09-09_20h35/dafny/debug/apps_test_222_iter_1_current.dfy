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
    decreases hi - lo + 1
{
    if lo > hi then [] else [lo*lo] + GenerateSquaresHelper(lo+1, hi)
}
function GenerateSquares(): seq<int>
{
    GenerateSquaresHelper(1, 44721)
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

function IntToString(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else IntToStringHelper(n)
}

function IsSubsequenceHelper(pattern: string, text: string, i: int, j: int): bool
    decreases |text| - j
{
    if i == |pattern| then true
    else if j == |text| then false
    else if pattern[i] == text[j] then IsSubsequenceHelper(pattern, text, i+1, j+1)
    else IsSubsequenceHelper(pattern, text, i, j+1)
}

function IsSubsequence(pattern: string, text: string): bool
{
    IsSubsequenceHelper(pattern, text, 0, 0)
}

// Additional simple facts to help verification
lemma {:auto} IntToStringHelper_nonempty(n: int)
    requires n > 0
    ensures |IntToStringHelper(n)| > 0
{
    if n / 10 != 0 {
        IntToStringHelper_nonempty(n / 10);
    }
}

lemma {:auto} GenerateSquaresHelper_positive(lo: int, hi: int)
    ensures forall k :: 0 <= k < |GenerateSquaresHelper(lo, hi)| ==> GenerateSquaresHelper(lo, hi)[k] > 0
{
    if lo > hi {
        // vacuously true
    } else {
        GenerateSquaresHelper_positive(lo+1, hi);
    }
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
            bestlen := |cur|;
            bestidx := i;
        }
        i := i + 1;
    }

    if bestlen == 0 {
        // no matching square as subsequence among all checked
        // show for all squares in sqs, not a subsequence
        assert forall idx :: 0 <= idx < |sqs| ==> |IntToString(sqs[idx])| > 0 by {
            var idx := 0;
            while idx < |sqs|
                invariant 0 <= idx <= |sqs|
                decreases |sqs| - idx
            {
                // Each element of sqs is a positive square
                // Use GenerateSquaresHelper_positive fact indirectly: GenerateSquares yields positive ints
                idx := idx + 1;
            }
        };
        assert forall idx :: 0 <= idx < |sqs| ==> !IsSubsequence(IntToString(sqs[idx]), s) by {
            var idx := 0;
            while idx < |sqs|
                invariant 0 <= idx <= |sqs|
                invariant forall k :: 0 <= k < idx ==> !IsSubsequence(IntToString(sqs[k]), s)
                decreases |sqs| - idx
            {
                var cur := IntToString(sqs[idx]);
                if IsSubsequence(cur, s) {
                    // From the loop invariant of the main loop we know that any subsequence found would have length <= bestlen (which is 0)
                    assert |cur| <= bestlen;
                    // But cur is non-empty since sqs[idx] > 0
                    assert |cur| > 0;
                    // contradiction, so this branch is impossible
                    assert false;
                }
                idx := idx + 1;
            }
        };
        result := -1;
    } else {
        // There is at least one matching square, witness at bestidx
        result := |s| - bestlen;
        // ensure the witnessed square satisfies the required properties
        assert 0 <= bestidx < |sqs|;
        assert IsSubsequence(IntToString(sqs[bestidx]), s);
        assert result == |s| - |IntToString(sqs[bestidx])|;
        // show minimality: any matching square has length <= bestlen
        assert forall idx :: 0 <= idx < |sqs| ==> (IsSubsequence(IntToString(sqs[idx]), s) ==> |IntToString(sqs[idx])| <= bestlen);
    }
}
// </vc-code>

