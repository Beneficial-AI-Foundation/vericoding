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
function GenerateSquaresHelper(start: int, maxn: int): seq<int>
  requires start >= 1
  ensures |GenerateSquaresHelper(start, maxn)| >= 0
  ensures forall i :: 0 <= i < |GenerateSquaresHelper(start, maxn)| ==> GenerateSquaresHelper(start, maxn)[i] > 0
  ensures forall i :: 0 <= i < |GenerateSquaresHelper(start, maxn)| ==> GenerateSquaresHelper(start, maxn)[i] == (start + i) * (start + i)
  ensures forall i :: 0 <= i < |GenerateSquaresHelper(start, maxn)| ==> GenerateSquaresHelper(start, maxn)[i] <= maxn
{
  if start * start > maxn then []
  else [start * start] + GenerateSquaresHelper(start + 1, maxn)
}

function IsSubsequenceHelper(pattern: string, text: string, i: int, j: int): bool
  requires 0 <= i <= |pattern|
  requires 0 <= j <= |text|
  ensures IsSubsequenceHelper(pattern, text, i, j) <==>
    i == |pattern| ||
    (exists k :: j <= k < |text| && pattern[i] == text[k] && IsSubsequenceHelper(pattern, text, i + 1, k + 1))
{
  if i == |pattern| then true
  else if j == |text| then false
  else if pattern[i] == text[j] then IsSubsequenceHelper(pattern, text, i + 1, j + 1)
  else IsSubsequenceHelper(pattern, text, i, j + 1)
}

function IntToStringHelper(n: int): string
  requires n > 0
  ensures |IntToStringHelper(n)| > 0
  ensures forall c :: c in IntToStringHelper(n) ==> '0' <= c <= '9'
{
  if n < 10 then [char(48 + n)]
  else IntToStringHelper(n / 10) + [char(48 + (n % 10))]
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
  var minLength := -1;
  var sqIndex := -1;
  var i := 0;
  while i < |squares|
    invariant 0 <= i <= |squares|
    invariant minLength == -1 || (0 <= sqIndex < i && squares[sqIndex] in squares && IsSubsequence(IntToString(squares[sqIndex]), s) && minLength == |IntToString(squares[sqIndex])| && forall k :: 0 <= k < i ==> (IsSubsequence(IntToString(squares[k]), s) ==> |IntToString(squares[k])| >= minLength))
    invariant if minLength == -1 then forall k :: 0 <= k < i ==> !IsSubsequence(IntToString(squares[k]), s)
  {
    var sq := squares[i];
    var sqStr := IntToString(sq);
    if IsSubsequence(sqStr, s) {
      if minLength == -1 || |sqStr| < minLength {
        minLength := |sqStr|;
        sqIndex := i;
      }
    }
    i := i + 1;
  }
  if minLength == -1 {
    result := -1;
  } else {
    result := |s| - minLength;
  }
}
// </vc-code>

