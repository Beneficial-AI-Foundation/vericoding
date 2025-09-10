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
function RepeatChar(c: char, count: nat): (result: string)
    ensures |result| == count
{
    if count == 0 then [] else c :: RepeatChar(c, count - 1)
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
    var result: seq<string> := [];
    for i := 0 to n - 1 {
        var line: string;
        if i <= magic {
            var stars := magic - i;
            var diamonds := n - 2 * stars;
            line := RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars);
        } else {
            var u := i - magic;
            var stars := u;
            var diamonds := n - 2 * stars;
            line := RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars);
        }
        result := result + [line];
    }
}
// </vc-code>

