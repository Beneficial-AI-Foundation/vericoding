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
{
    if count == 0 then ""
    else [c] + RepeatChar(c, count - 1)
}

lemma RepeatCharLength(c: char, count: int)
    requires count >= 0
    ensures |RepeatChar(c, count)| == count
{
    if count == 0 {
    } else {
        RepeatCharLength(c, count - 1);
    }
}

lemma RepeatCharConcat(c1: char, c2: char, count1: int, count2: int)
    requires count1 >= 0 && count2 >= 0
    ensures RepeatChar(c1, count1) + RepeatChar(c2, count2) == RepeatChar(c1, count1) + RepeatChar(c2, count2)
{
}

lemma RowLengthCorrect(n: int, i: int)
    requires n >= 3 && n % 2 == 1
    requires 0 <= i < n
    ensures var magic := (n - 1) / 2;
            var stars := if i <= magic then magic - i else i - magic;
            var diamonds := n - 2 * stars;
            stars >= 0 && diamonds >= 0 && 2 * stars + diamonds == n
{
    var magic := (n - 1) / 2;
    var stars := if i <= magic then magic - i else i - magic;
    var diamonds := n - 2 * stars;
    
    if i <= magic {
        assert stars == magic - i >= 0;
    } else {
        assert stars == i - magic >= 0;
    }
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
    result := [];
    
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> |result[j]| == n
        invariant forall j :: 0 <= j < i && j <= magic ==> 
            var stars := magic - j;
            var diamonds := n - 2 * stars;
            result[j] == RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars)
        invariant forall j :: 0 <= j < i && magic < j ==> 
            var u := j - magic;
            var stars := u;
            var diamonds := n - 2 * stars;
            result[j] == RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars)
    {
        var stars: int;
        if i <= magic {
            stars := magic - i;
        } else {
            stars := i - magic;
        }
        
        var diamonds := n - 2 * stars;
        
        RowLengthCorrect(n, i);
        
        var row := RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars);
        
        RepeatCharLength('*', stars);
        RepeatCharLength('D', diamonds);
        RepeatCharLength('*', stars);
        
        result := result + [row];
        i := i + 1;
    }
}
// </vc-code>

