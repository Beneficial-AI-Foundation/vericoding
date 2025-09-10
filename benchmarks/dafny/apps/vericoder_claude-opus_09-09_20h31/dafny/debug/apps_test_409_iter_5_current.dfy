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
    ensures FindIndex(s, pattern) < 0 ==> FindIndex(s, pattern) == -1
    ensures FindIndex(s, pattern) != -1 ==> FindIndex(s, pattern) >= 0
{
    if |pattern| == 0 || |s| < |pattern| {
        // Base case
    } else if s[..|pattern|] == pattern {
        // Found at beginning
    } else {
        var rest := FindIndex(s[1..], pattern);
        if rest >= 0 {
            FindIndexProperties(s[1..], pattern);
        } else {
            FindIndexProperties(s[1..], pattern);
        }
    }
}

lemma CountSubstringZeroImpliesNoOccurrence(s: string, pattern: string)
    ensures CountSubstring(s, pattern) == 0 ==> FindIndex(s, pattern) == -1
    ensures FindIndex(s, pattern) >= 0 ==> CountSubstring(s, pattern) > 0
    ensures FindIndex(s, pattern) == -1 ==> CountSubstring(s, pattern) == 0
{
    if |pattern| == 0 || |s| < |pattern| {
        // Base case
    } else if s[..|pattern|] == pattern {
        // Found at beginning
    } else {
        CountSubstringZeroImpliesNoOccurrence(s[1..], pattern);
    }
}

lemma HasNonOverlappingRequiresBothPatterns(s: string)
    ensures HasNonOverlappingABAndBA(s) ==> (FindIndex(s, "AB") >= 0 && FindIndex(s, "BA") >= 0)
    ensures (FindIndex(s, "AB") < 0 || FindIndex(s, "BA") < 0) ==> !HasNonOverlappingABAndBA(s)
{
    var abIndex := FindIndex(s, "AB");
    var baIndex := FindIndex(s, "BA");
    
    // By definition of HasNonOverlappingABAndBA, it requires both indices to be >= 0
    if HasNonOverlappingABAndBA(s) {
        assert abIndex >= 0 && baIndex >= 0;
    }
    
    if abIndex < 0 || baIndex < 0 {
        // If either index is negative, the first conjunct (abIndex >= 0 && baIndex >= 0) is false
        // Therefore HasNonOverlappingABAndBA(s) is false
        assert !HasNonOverlappingABAndBA(s);
    }
}

lemma HasNonOverlappingEquivalence(s: string)
    ensures HasNonOverlappingABAndBA(s) <==> 
            (var abIndex := FindIndex(s, "AB");
             var baIndex := FindIndex(s, "BA");
             (abIndex >= 0 && baIndex >= 0) &&
             ((abIndex >= 0 && abIndex + 2 < |s| && CountSubstring(s[abIndex + 2..], "BA") > 0) ||
              (baIndex >= 0 && baIndex + 2 < |s| && CountSubstring(s[baIndex + 2..], "AB") > 0)))
{
    // This follows directly from the definition of HasNonOverlappingABAndBA
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
    
    CountSubstringZeroImpliesNoOccurrence(s, "AB");
    CountSubstringZeroImpliesNoOccurrence(s, "BA");
    HasNonOverlappingRequiresBothPatterns(s);
    FindIndexProperties(s, "AB");
    FindIndexProperties(s, "BA");
    
    if abIndex == -1 || baIndex == -1 {
        if abIndex == -1 {
            assert CountSubstring(s, "AB") == 0;
        }
        if baIndex == -1 {
            assert CountSubstring(s, "BA") == 0;
        }
        assert CountSubstring(s, "AB") == 0 || CountSubstring(s, "BA") == 0;
        assert !HasNonOverlappingABAndBA(s);
        result := "NO";
    } else {
        assert abIndex != -1 && baIndex != -1;
        assert abIndex >= 0;
        assert baIndex >= 0;
        
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
        
        assert hasNonOverlapping == ((abIndex >= 0 && abIndex + 2 < |s| && CountSubstring(s[abIndex + 2..], "BA") > 0) ||
                                     (baIndex >= 0 && baIndex + 2 < |s| && CountSubstring(s[baIndex + 2..], "AB") > 0));
        
        if hasNonOverlapping {
            assert abIndex >= 0 && baIndex >= 0;
            assert (abIndex >= 0 && abIndex + 2 < |s| && CountSubstring(s[abIndex + 2..], "BA") > 0) ||
                   (baIndex >= 0 && baIndex + 2 < |s| && CountSubstring(s[baIndex + 2..], "AB") > 0);
            assert HasNonOverlappingABAndBA(s);
            result := "YES";
        } else {
            assert CountSubstring(s, "AB") > 0 && CountSubstring(s, "BA") > 0;
            assert !((abIndex >= 0 && abIndex + 2 < |s| && CountSubstring(s[abIndex + 2..], "BA") > 0) ||
                     (baIndex >= 0 && baIndex + 2 < |s| && CountSubstring(s[baIndex + 2..], "AB") > 0));
            assert !HasNonOverlappingABAndBA(s);
            result := "NO";
        }
    }
}
// </vc-code>

