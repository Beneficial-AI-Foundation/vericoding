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
    ensures |RepeatChar(c, count)| == count
    ensures forall i :: 0 <= i < count ==> RepeatChar(c, count)[i] == c
{
    if count == 0 then ""
    else [c] + RepeatChar(c, count - 1)
}

lemma RepeatCharLength(c: char, count: nat)
    ensures |RepeatChar(c, count)| == count
{
    // Follows directly from the ensures clause of RepeatChar
}

lemma RepeatCharComposition(c: char, a: nat, b: nat)
    ensures RepeatChar(c, a) + RepeatChar(c, b) == RepeatChar(c, a + b)
{
    if a == 0 {
        assert RepeatChar(c, a) + RepeatChar(c, b) == "" + RepeatChar(c, b) == RepeatChar(c, b) == RepeatChar(c, a + b);
    } else {
        calc {
            RepeatChar(c, a) + RepeatChar(c, b);
            == ([c] + RepeatChar(c, a - 1)) + RepeatChar(c, b);
            == [c] + (RepeatChar(c, a - 1) + RepeatChar(c, b));
            == { RepeatCharComposition(c, a - 1, b); }
               [c] + RepeatChar(c, a - 1 + b);
            == RepeatChar(c, a + b);
        }
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
        invariant forall j :: 0 <= j <= magic && j < i ==> 
            var stars := magic - j;
            var diamonds := n - 2 * stars;
            result[j] == RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars)
        invariant forall j :: magic + 1 <= j < i ==> 
            var u := j - magic;
            var stars := u;
            var diamonds := n - 2 * stars;
            result[j] == RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars)
    {
        var row: string;
        if i <= magic {
            var stars := magic - i;
            var diamonds := n - 2 * stars;
            row := RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars);
            assert |row| == stars + diamonds + stars == stars + (n - 2 * stars) + stars == n;
        } else {
            var u := i - magic;
            var stars := u;
            var diamonds := n - 2 * stars;
            row := RepeatChar('*', stars) + RepeatChar('D', diamonds) + RepeatChar('*', stars);
            assert |row| == stars + diamonds + stars == stars + (n - 2 * stars) + stars == n;
        }
        
        result := result + [row];
        i := i + 1;
    }
}
// </vc-code>

