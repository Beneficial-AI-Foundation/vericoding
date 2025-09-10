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
function GenerateSquaresHelper(n: int, limit: int): seq<int>
    requires n >= 1
    requires limit >= 1
    ensures forall i :: 0 <= i < |GenerateSquaresHelper(n, limit)| ==> GenerateSquaresHelper(n, limit)[i] > 0
    decreases limit - n + 1
{
    if n > limit then []
    else [n * n] + GenerateSquaresHelper(n + 1, limit)
}

function IsSubsequenceHelper(pattern: string, text: string, i: int, j: int): bool
    requires 0 <= i <= |pattern|
    requires 0 <= j <= |text|
    decreases |pattern| - i, |text| - j
{
    if i == |pattern| then true
    else if j == |text| then false
    else if pattern[i] == text[j] then IsSubsequenceHelper(pattern, text, i + 1, j + 1)
    else IsSubsequenceHelper(pattern, text, i, j + 1)
}

function IntToStringHelper(n: int): string
    requires n > 0
    decreases n
{
    if n < 10 then 
        [('0' as char) + (n as char)]
    else 
        IntToStringHelper(n / 10) + [('0' as char) + ((n % 10) as char)]
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
    var minToRemove := -1;
    var i := 0;
    
    while i < |squares|
        invariant 0 <= i <= |squares|
        invariant minToRemove == -1 || minToRemove >= 0
        invariant minToRemove == -1 ==> forall k :: 0 <= k < i ==> !IsSubsequence(IntToString(squares[k]), s)
        invariant minToRemove >= 0 ==> exists k :: 0 <= k < |squares| && IsSubsequence(IntToString(squares[k]), s) && minToRemove == |s| - |IntToString(squares[k])|
        invariant minToRemove >= 0 ==> forall k :: 0 <= k < i && IsSubsequence(IntToString(squares[k]), s) ==> |s| - |IntToString(squares[k])| >= minToRemove
    {
        var sqStr := IntToString(squares[i]);
        if IsSubsequence(sqStr, s) {
            var toRemove := |s| - |sqStr|;
            if minToRemove == -1 || toRemove < minToRemove {
                minToRemove := toRemove;
            }
        }
        i := i + 1;
    }
    
    result := minToRemove;
}
// </vc-code>

