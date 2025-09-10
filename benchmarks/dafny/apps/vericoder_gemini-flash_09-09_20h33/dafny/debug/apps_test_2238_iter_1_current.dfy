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
function RepeatChar(c: char, count: int) : string
  requires count >= 0
  ensures |RepeatChar(c, count)| == count
{
  if count == 0 then ""
  else (var s := RepeatChar(c, count - 1); s + c)
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
    var result_array: array<string> := new string[n];
    var magic := (n - 1) / 2;

    // First half (including middle): rows 0 to magic
    var i := 0;
    while i <= magic
        invariant 0 <= i <= magic + 1
        invariant forall k :: 0 <= k < i ==>
            var stars_k := magic - k;
            var diamonds_k := n - 2 * stars_k;
            result_array[k] == RepeatChar('*', stars_k) + RepeatChar('D', diamonds_k) + RepeatChar('*', stars_k)
    {
        var stars := magic - i;
        var diamonds := n - 2 * stars;
        result_array[i] := RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars);
        i := i + 1;
    }

    // Second half: rows magic+1 to n-1
    while i < n
        invariant magic + 1 <= i <= n
        invariant forall k :: 0 <= k < magic + 1 ==>
            var stars_k := magic - k;
            var diamonds_k := n - 2 * stars_k;
            result_array[k] == RepeatChar('*', stars_k) + RepeatChar('D', diamonds_k) + RepeatChar('*', stars_k)
        invariant forall k :: magic + 1 <= k < i ==>
            var u_k := k - magic;
            var stars_k := u_k;
            var diamonds_k := n - 2 * stars_k;
            result_array[k] == RepeatChar('*', stars_k) + RepeatChar('D', diamonds_k) + RepeatChar('*', stars_k)
    {
        var u := i - magic;
        assert u > 0; // Ensures u is positive for stars count
        var stars := u;
        var diamonds := n - 2 * stars;
        result_array[i] := RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars);
        i := i + 1;
    }

    result := result_array[..];
}
// </vc-code>

