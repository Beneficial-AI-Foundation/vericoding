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
lemma FindIndexProperties(s: string, pattern: string)
    ensures FindIndex(s, pattern) >= 0 ==> FindIndex(s, pattern) + |pattern| <= |s|
    ensures FindIndex(s, pattern) >= 0 ==> s[FindIndex(s, pattern)..FindIndex(s, pattern) + |pattern|] == pattern
{
    if |pattern| == 0 || |s| < |pattern| {
        // Base case
    } else if s[..|pattern|] == pattern {
        // Found at beginning
    } else {
        var rest := FindIndex(s[1..], pattern);
        if rest >= 0 {
            FindIndexProperties(s[1..], pattern);
        }
    }
}

lemma CountSubstringZeroImpliesNoOccurrence(s: string, pattern: string)
    ensures CountSubstring(s, pattern) == 0 ==> FindIndex(s, pattern) == -1
    ensures FindIndex(s, pattern) >= 0 ==> CountSubstring(s, pattern) > 0
{
    if |pattern| == 0 || |s| < |pattern| {
        // Base case
    } else if s[..|pattern|] == pattern {
        // Found at beginning
    } else {
        CountSubstringZeroImpliesNoOccurrence(s[1..], pattern);
    }
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
    
    var abIndex := FindIndex(s, "AB");
    var baIndex := FindIndex(s, "BA");
    
    if abIndex == -1 || baIndex == -1 {
        CountSubstringZeroImpliesNoOccurrence(s, "AB");
        CountSubstringZeroImpliesNoOccurrence(s, "BA");
        result := "NO";
    } else {
        FindIndexProperties(s, "AB");
        FindIndexProperties(s, "BA");
        
        var hasNonOverlapping := false;
        
        // Check if we can find BA after AB (non-overlapping)
        if abIndex >= 0 && abIndex + 2 < |s| {
            var countBAAfterAB := CountSubstring(s[abIndex + 2..], "BA");
            if countBAAfterAB > 0 {
                hasNonOverlapping := true;
            }
        }
        
        // Check if we can find AB after BA (non-overlapping)
        if !hasNonOverlapping && baIndex >= 0 && baIndex + 2 < |s| {
            var countABAfterBA := CountSubstring(s[baIndex + 2..], "AB");
            if countABAfterBA > 0 {
                hasNonOverlapping := true;
            }
        }
        
        if hasNonOverlapping {
            result := "YES";
        } else {
            result := "NO";
        }
    }
}
// </vc-code>

