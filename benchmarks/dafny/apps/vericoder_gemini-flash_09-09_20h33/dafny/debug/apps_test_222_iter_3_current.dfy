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
    requires n > 0
    requires limit > 0
    decreases limit - n + 1 // Add 1 to ensure termination when n = limit
    ensures forall i :: 0 <= i < |GenerateSquaresHelper(n, limit)| ==> GenerateSquaresHelper(n, limit)[i] > 0
{
    if n * n > limit
    then []
    else [n * n] + GenerateSquaresHelper(n + 1, limit)
}

function IsSubsequenceHelper(pattern: string, text: string, p_idx: int, t_idx: int): bool
    requires 0 <= p_idx <= |pattern|
    requires 0 <= t_idx <= |text|
    decreases (|pattern| - p_idx) + (|text| - t_idx)
{
    if p_idx == |pattern| then
        true
    else if t_idx == |text| then
        false
    else if pattern[p_idx] == text[t_idx] then
        IsSubsequenceHelper(pattern, text, p_idx + 1, t_idx + 1)
    else
        IsSubsequenceHelper(pattern, text, p_idx, t_idx + 1)
}

function IntToStringHelper(n: int): string
    requires n > 0
    decreases n
{
    if n == 0 then
        ""
    else
        // Convert the last digit to a character (string)
        // and append it to the result of the rest of the number
        IntToStringHelper(n / 10) + (n % 10).ToString()
    // A more explicit way to convert a digit to string:
    // var digit_char: char := (('0' as int) + (n % 10)) as char;
    // IntToStringHelper(n / 10) + [digit_char];
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
    var min_diff := -1;

    var i := 0;
    while i < |squares|
        invariant 0 <= i <= |squares|
        invariant min_diff == -1 || min_diff >= 0
        invariant min_diff == -1 ==> (forall k :: 0 <= k < i ==> !IsSubsequence(IntToString(squares[k]), s))
        invariant min_diff >= 0 ==> (exists sq_idx :: 0 <= sq_idx < i && IsSubsequence(IntToString(squares[sq_idx]), s) && min_diff == |s| - |IntToString(squares[sq_idx])|)
        invariant min_diff >= 0 ==> (forall k :: 0 <= k < i && IsSubsequence(IntToString(squares[k]), s) ==> |s| - |IntToString(squares[k])| >= min_diff)
    {
        var sq_str := IntToString(squares[i]);
        if IsSubsequence(sq_str, s) {
            var current_diff := |s| - |sq_str|;
            if min_diff == -1 || current_diff < min_diff {
                min_diff := current_diff;
            }
        }
        i := i + 1;
    }
    result := min_diff;
}
// </vc-code>

