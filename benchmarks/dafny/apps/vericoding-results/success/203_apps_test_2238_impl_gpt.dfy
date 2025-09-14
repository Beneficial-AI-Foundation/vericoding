predicate ValidInput(n: int)
{
    n >= 3 && n <= 101 && n % 2 == 1
}

predicate ValidResult(result: seq<string>, n: int)
{
    |result| == n &&
    forall i :: 0 <= i < |result| ==> |result[i]| == n
}

predicate CorrectDiamondPattern(result: seq<string>, n: int)
{
    |result| == n ==> (
    var magic := (n - 1) / 2;
    // First half (including middle): rows 0 to magic
    (forall i :: 0 <= i <= magic && i < |result| ==> 
        var stars := magic - i;
        var diamonds := n - 2 * stars;
        result[i] == RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars)) &&
    // Second half: rows magic+1 to n-1
    (forall i :: magic + 1 <= i < n && i < |result| ==> 
        var u := i - magic;
        var stars := u;
        var diamonds := n - 2 * stars;
        result[i] == RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars))
    )
}

// <vc-helpers>
function RepeatChar(c: char, k: int): string
  requires 0 <= k
  requires c == '*' || c == 'D'
  decreases k
  ensures |RepeatChar(c, k)| == k
{
  if k == 0 then "" else if c == '*' then "*" + RepeatChar(c, k - 1) else "D" + RepeatChar(c, k - 1)
}

function RowString(n: int, i: int): string
  requires ValidInput(n)
  requires 0 <= i < n
  ensures |RowString(n, i)| == n
  ensures
    var magic := (n - 1) / 2;
    i <= magic ==>
      var stars := magic - i;
      var diamonds := n - 2 * stars;
      RowString(n, i) == RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars)
  ensures
    var magic := (n - 1) / 2;
    i >= magic + 1 ==>
      var u := i - magic;
      var stars := u;
      var diamonds := n - 2 * stars;
      RowString(n, i) == RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars)
{
  var magic := (n - 1) / 2;
  var stars := if i <= magic then magic - i else i - magic;
  var diamonds := n - 2 * stars;
  RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<string>)
    requires ValidInput(n)
    ensures ValidResult(result, n)
    ensures CorrectDiamondPattern(result, n)
// </vc-spec>
// <vc-code>
{
  var s: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |s| == i
    invariant forall j :: 0 <= j < |s| ==> s[j] == RowString(n, j)
    decreases n - i
  {
    s := s + [RowString(n, i)];
    i := i + 1;
  }
  result := s;
}
// </vc-code>

