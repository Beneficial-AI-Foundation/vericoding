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
lemma CountSubstringZeroImpliesNotFound(s: string, pattern: string)
    requires |pattern| > 0
    ensures CountSubstring(s, pattern) == 0 <==> FindIndex(s, pattern) == -1
{
    if |s| < |pattern| {
        assert CountSubstring(s, pattern) == 0;
        assert FindIndex(s, pattern) == -1;
    } else {
        if s[..|pattern|] == pattern {
            assert CountSubstring(s, pattern) >= 1;
            assert FindIndex(s, pattern) == 0;
        } else {
            CountSubstringZeroImpliesNotFound(s[1..], pattern);
            assert CountSubstring(s, pattern) == CountSubstring(s[1..], pattern);
            var rest := FindIndex(s[1..], pattern);
            assert FindIndex(s, pattern) == (if rest == -1 then -1 else 1 + rest);
        }
    }
}

lemma CountSubstringPositiveImpliesFound(s: string, pattern: string)
    requires |pattern| > 0
    ensures CountSubstring(s, pattern) > 0 <==> FindIndex(s, pattern) >= 0
{
    CountSubstringZeroImpliesNotFound(s, pattern);
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
    
    var abCount := CountSubstring(s, "AB");
    var baCount := CountSubstring(s, "BA");
    
    if abCount == 0 || baCount == 0 {
        result := "NO";
    } else {
        CountSubstringPositiveImpliesFound(s, "AB");
        CountSubstringPositiveImpliesFound(s, "BA");
        
        var abIndex := FindIndex(s, "AB");
        var baIndex := FindIndex(s, "BA");
        
        var hasNonOverlapping := 
            (abIndex >= 0 && abIndex + 2 < |s| && CountSubstring(s[abIndex + 2..], "BA") > 0) ||
            (baIndex >= 0 && baIndex + 2 < |s| && CountSubstring(s[baIndex + 2..], "AB") > 0);
            
        if hasNonOverlapping {
            result := "YES";
        } else {
            result := "NO";
        }
    }
}
// </vc-code>

