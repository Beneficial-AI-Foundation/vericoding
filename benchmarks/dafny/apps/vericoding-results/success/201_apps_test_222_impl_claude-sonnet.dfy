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
function GenerateSquaresHelper(i: int, limit: int): seq<int>
    requires i >= 1
    requires limit >= 1
    decreases limit - i
    ensures forall k :: 0 <= k < |GenerateSquaresHelper(i, limit)| ==> GenerateSquaresHelper(i, limit)[k] > 0
{
    if i > limit then []
    else [i * i] + GenerateSquaresHelper(i + 1, limit)
}

function IsSubsequenceHelper(pattern: string, text: string, pIndex: int, tIndex: int): bool
    requires 0 <= pIndex <= |pattern|
    requires 0 <= tIndex <= |text|
    decreases |pattern| - pIndex, |text| - tIndex
{
    if pIndex == |pattern| then true
    else if tIndex == |text| then false
    else if pattern[pIndex] == text[tIndex] then
        IsSubsequenceHelper(pattern, text, pIndex + 1, tIndex + 1)
    else
        IsSubsequenceHelper(pattern, text, pIndex, tIndex + 1)
}

function IntToStringHelper(n: int): string
    requires n > 0
    decreases n
{
    if n < 10 then [('0' as int + n) as char]
    else IntToStringHelper(n / 10) + [('0' as int + (n % 10)) as char]
}

lemma IntToStringPositive(n: int)
    requires n > 0
    ensures |IntToString(n)| > 0
{
}

lemma IsSubsequenceImpliesLengthBound(pattern: string, text: string)
    requires IsSubsequence(pattern, text)
    ensures |pattern| <= |text|
{
    IsSubsequenceImpliesLengthBoundHelper(pattern, text, 0, 0);
}

lemma IsSubsequenceImpliesLengthBoundHelper(pattern: string, text: string, pIndex: int, tIndex: int)
    requires 0 <= pIndex <= |pattern|
    requires 0 <= tIndex <= |text|
    requires IsSubsequenceHelper(pattern, text, pIndex, tIndex)
    ensures |pattern| - pIndex <= |text| - tIndex
    decreases |pattern| - pIndex, |text| - tIndex
{
    if pIndex == |pattern| {
    } else if tIndex == |text| {
    } else if pattern[pIndex] == text[tIndex] {
        IsSubsequenceImpliesLengthBoundHelper(pattern, text, pIndex + 1, tIndex + 1);
    } else {
        IsSubsequenceImpliesLengthBoundHelper(pattern, text, pIndex, tIndex + 1);
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
    var squares := GenerateSquares();
    var minRemoval := -1;
    var i := 0;
    
    while i < |squares|
        invariant 0 <= i <= |squares|
        invariant minRemoval >= -1
        invariant minRemoval == -1 ==> forall j :: 0 <= j < i ==> !IsSubsequence(IntToString(squares[j]), s)
        invariant minRemoval >= 0 ==> exists j :: 0 <= j < i && IsSubsequence(IntToString(squares[j]), s) && minRemoval == |s| - |IntToString(squares[j])|
        invariant minRemoval >= 0 ==> forall j :: 0 <= j < i && IsSubsequence(IntToString(squares[j]), s) ==> |s| - |IntToString(squares[j])| >= minRemoval
    {
        var squareStr := IntToString(squares[i]);
        if IsSubsequence(squareStr, s) {
            IsSubsequenceImpliesLengthBound(squareStr, s);
            var removal := |s| - |squareStr|;
            if minRemoval == -1 || removal < minRemoval {
                minRemoval := removal;
            }
        }
        i := i + 1;
    }
    
    result := minRemoval;
}
// </vc-code>

