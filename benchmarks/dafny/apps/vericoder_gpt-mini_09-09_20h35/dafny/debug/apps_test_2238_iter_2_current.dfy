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
function RepeatChar(c: char, count: int): string
    requires count >= 0
    ensures |RepeatChar(c, count)| == count
    ensures forall i :: 0 <= i < count ==> RepeatChar(c, count)[i] == c
    decreases count
{
    if count == 0 then "" else RepeatChar(c, count - 1) + c.ToString()
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
  var magic := (n - 1) / 2;
  var a := new string[n];
  var i := 0;
  // Fill first half including middle: rows 0..magic
  while i <= magic
    invariant 0 <= i <= magic + 1
    invariant forall k :: 0 <= k < i ==>
        var stars := magic - k;
        var diamonds := n - 2 * stars;
        a[k] == RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars)
  {
    var stars := magic - i;
    var diamonds := n - 2 * stars;
    a[i] := RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars);
    i := i + 1;
  }

  // Fill second half: rows magic+1 .. n-1
  i := magic + 1;
  while i < n
    invariant magic + 1 <= i <= n
    invariant forall k :: 0 <= k < i ==>
      if k <= magic then
        var stars := magic - k;
        var diamonds := n - 2 * stars;
        a[k] == RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars)
      else
        var u := k - magic;
        var stars2 := u;
        var diamonds2 := n - 2 * stars2;
        a[k] == RepeatChar('*', stars2) + RepeatChar('D', diamonds2) + RepeatChar('*', stars2)
  {
    var u := i - magic;
    var stars := u;
    var diamonds := n - 2 * stars;
    a[i] := RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars);
    i := i + 1;
  }

  result := a[..];
}
// </vc-code>

