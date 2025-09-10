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
{
    if count == 0 then "" 
    else RepeatChar(c, count - 1) + [c]
}

lemma RepeatCharProperties()
    ensures |RepeatChar('*', 0)| == 0
    ensures |RepeatChar('*', 3)| == 3
    ensures forall i :: 0 <= i < 3 ==> RepeatChar('*', 3)[i] == '*'
{
}

ghost method VerifyRepeatChar()
{
    var s := RepeatChar('D', 5);
    assert |s| == 5;
    assert forall i :: 0 <= i < 5 ==> s[i] == 'D';
}

lemma DiamondPatternSymmetryLemma(result: seq<string>, n: int, i: int, magic: int)
    requires 0 <= i <= n
    requires magic == (n - 1) / 2
    requires |result| == i
    requires forall j :: 0 <= j < i ==> 
        if j <= magic
        then result[j] == RepeatChar('*', magic - j) + RepeatChar('D', n - 2*(magic - j)) + RepeatChar('*', magic - j)
        else result[j] == RepeatChar('*', j - magic) + RepeatChar('D', n - 2*(j - magic)) + RepeatChar('*', j - magic)
    ensures CorrectDiamondPattern(result, n)
{
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
    var i := 0;
    result := [];

    while i < n
        invariant 0 <= i <= n
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> |result[j]| == n
        invariant forall j :: 0 <= j < i ==> 
            if j <= magic
            then result[j] == RepeatChar('*', magic - j) + RepeatChar('D', n - 2*(magic - j)) + RepeatChar('*', magic - j)
            else result[j] == RepeatChar('*', j - magic) + RepeatChar('D', n - 2*(j - magic)) + RepeatChar('*', j - magic)
    {
        var stars: int;
        var diamonds: int;
        
        if i <= magic {
            stars := magic - i;
            diamonds := n - 2 * stars;
        } else {
            var u := i - magic;
            stars := u;
            diamonds := n - 2 * stars;
        }
        
        var row := RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars);
        result := result + [row];
        i := i + 1;
    }
    DiamondPatternSymmetryLemma(result, n, n, magic);
}
// </vc-code>

