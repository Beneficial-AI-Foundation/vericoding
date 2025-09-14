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
function RepeatChar(c: char, count: nat): string
{
    seq(count, i => c)
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
  result := [];
  var magic := (n - 1) / 2;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> |result[j]| == n
    invariant forall j :: 0 <= j < i && j <= magic ==>
        var stars := magic - j;
        var diamonds := n - 2 * stars;
        result[j] == RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars)
    invariant forall j :: magic + 1 <= j < i ==>
        var stars := j - magic;
        var diamonds := n - 2 * stars;
        result[j] == RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars)
  {
    if i <= magic {
        var stars := magic - i;
        var diamonds := n - 2 * stars;
        var row := RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars);
        result := result + [row];
    } else {
        var stars := i - magic;
        var diamonds := n - 2 * stars;
        var row := RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars);
        result := result + [row];
    }
    i := i + 1;
  }
}
// </vc-code>

