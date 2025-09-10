function CountSubstring(s: string, pattern: string): nat
{
    if |pattern| == 0 || |s| < |pattern| then 0
    else if s[..|pattern|] == pattern then 1 + CountSubstring(s[1..], pattern)
    else CountSubstring(s[1..], pattern)
}

function FindIndex(s: string, pattern: string): int
{
    if |pattern| == 0 || |s| < |pattern| then -1
    else if s[..|pattern|] == pattern then 0
    else 
        var rest := FindIndex(s[1..], pattern);
        if rest == -1 then -1 else 1 + rest
}

predicate HasNonOverlappingABAndBA(s: string)
{
    var abIndex := FindIndex(s, "AB");
    var baIndex := FindIndex(s, "BA");

    (abIndex >= 0 && baIndex >= 0) &&
    (
        (abIndex >= 0 && abIndex + 2 < |s| && CountSubstring(s[abIndex + 2..], "BA") > 0) ||
        (baIndex >= 0 && baIndex + 2 < |s| && CountSubstring(s[baIndex + 2..], "AB") > 0)
    )
}

predicate ValidInput(input: string)
{
    |input| >= 0
}

// <vc-helpers>
lemma CorrectFind(s: string, p: string)
    ensures (CountSubstring(s, p) > 0) <==> (FindIndex(s, p) >= 0)
    decreases |s|
{
    if |p| == 0 || |s| < |p| {
        assert CountSubstring(s, p) == 0;
        assert FindIndex(s, p) == -1;
    } else if s[..|p|] == p {
        assert true;
    } else {
        CorrectFind(s[1..], p);
        assert CountSubstring(s, p) == CountSubstring(s[1..], p);
        assert FindIndex(s, p) == if FindIndex(s[1..], p) == -1 then -1 else 1 + FindIndex(s[1..], p);
        if CountSubstring(s[1..], p) > 0 {
            assert FindIndex(s[1..], p) >= 0;
            assert FindIndex(s, p) >= 0;
        } else {
            assert CountSubstring(s[1..], p) == 0;
            assert !(FindIndex(s[1..], p) >= 0);
            assert FindIndex(s[1..], p) == -1;
            assert FindIndex(s, p) == -1;
        }
    }
}

method ComputeHas(s: string) returns (b: bool)
    ensures b <==> HasNonOverlappingABAndBA(s)
{
    var abIndex := FindIndex(s, "AB");
    var baIndex := FindIndex(s, "BA");
    if abIndex >= 0 && baIndex >= 0 {
        var hasABthenBA := abIndex + 2 < |s| && CountSubstring(s[abIndex + 2..], "BA") > 0;
        var hasBAthenAB := baIndex + 2 < |s| && CountSubstring(s[baIndex + 2..], "AB") > 0;
        b := hasABthenBA || hasBAthenAB;
    } else {
        b := false;
    }
    // Assert using the lemma to help verification
    CorrectFind(s, "AB");
    CorrectFind(s, "BA");
    assert ((CountSubstring(s, "AB") > 0) <==> (FindIndex(s, "AB") >= 0));
    assert ((CountSubstring(s, "BA") > 0) <==> (FindIndex(s, "BA") >= 0));
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == "YES" <==> HasNonOverlappingABAndBA(if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input)
    ensures result == "YES" || result == "NO"
    ensures (var s := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
             CountSubstring(s, "AB") == 0 || CountSubstring(s, "BA") == 0) ==> result == "NO"
    ensures (var s := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
             var abIndex := FindIndex(s, "AB");
             var baIndex := FindIndex(s, "BA");
             CountSubstring(s, "AB") > 0 && CountSubstring(s, "BA") > 0 &&
             !((abIndex >= 0 && abIndex + 2 < |s| && CountSubstring(s[abIndex + 2..], "BA") > 0) ||
               (baIndex >= 0 && baIndex + 2 < |s| && CountSubstring(s[baIndex + 2..], "AB") > 0))) ==> result == "NO"
// </vc-spec>
// <vc-code>
{
    var s := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    CorrectFind(s, "AB");
    CorrectFind(s, "BA");
    var b := ComputeHas(s);
    if b {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

