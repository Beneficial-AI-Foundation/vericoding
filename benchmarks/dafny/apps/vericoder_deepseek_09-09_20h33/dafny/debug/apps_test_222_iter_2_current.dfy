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
function GenerateSquaresHelper(start: int, count: int): seq<int>
  requires start >= 1
  requires count >= 0
  ensures forall i :: 0 <= i < |result| ==> result[i] > 0
  ensures |result| == count
  ensures forall i :: 0 <= i < count ==> result[i] == (start + i) * (start + i)
{
  if count == 0 then []
  else [start * start] + GenerateSquaresHelper(start + 1, count - 1)
}

function IsSubsequenceHelper(pattern: string, text: string, pIdx: int, tIdx: int): bool
  requires 0 <= pIdx <= |pattern|
  requires 0 <= tIdx <= |text|
{
  if pIdx >= |pattern| then true
  else if tIdx >= |text| then false
  else if pattern[pIdx] == text[tIdx] then IsSubsequenceHelper(pattern, text, pIdx + 1, tIdx + 1)
  else IsSubsequenceHelper(pattern, text, pIdx, tIdx + 1)
}

function IntToStringHelper(n: int): string
  requires n > 0
  decreases n
{
  if n < 10 then [Dafny_digit(n)]
  else IntToStringHelper(n / 10) + [Dafny_digit(n % 10)]
}

function Dafny_digit(n: int): char
  requires 0 <= n <= 9
  ensures '0' <= result <= '9'
{
  if n == 0 then '0'
  else if n == 1 then '1'
  else if n == 2 then '2'
  else if n == 3 then '3'
  else if n == 4 then '4'
  else if n == 5 then '5'
  else if n == 6 then '6'
  else if n == 7 then '7'
  else if n == 8 then '8'
  else '9'
}

lemma GenerateSquaresValid()
  ensures forall i :: 0 <= i < |GenerateSquares()| ==> GenerateSquares()[i] > 0
{
  // Lemma body can be empty since the function definition already provides the guarantee
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
  var best := -1;
  var i := 0;
  while i < |squares|
    invariant 0 <= i <= |squares|
    invariant best == -1 ==> forall j :: 0 <= j < i ==> !IsSubsequence(IntToString(squares[j]), s)
    invariant best >= 0 ==> exists j :: 0 <= j < i && IsSubsequence(IntToString(squares[j]), s) && |s| - |IntToString(squares[j])| == best
    invariant best >= 0 ==> forall j :: 0 <= j < i && IsSubsequence(IntToString(squares[j]), s) ==> |s| - |IntToString(squares[j])| >= best
  {
    var sqStr := IntToString(squares[i]);
    if IsSubsequence(sqStr, s) {
      var deletions := |s| - |sqStr|;
      if best == -1 || deletions < best {
        best := deletions;
      }
    }
    i := i + 1;
  }
  return best;
}
// </vc-code>

