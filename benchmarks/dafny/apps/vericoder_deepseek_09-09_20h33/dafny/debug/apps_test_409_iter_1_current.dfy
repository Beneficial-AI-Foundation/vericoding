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
lemma FindIndexCountSubstring(s: string, pattern: string)
  requires |pattern| > 0
  ensures FindIndex(s, pattern) >= 0 <==> CountSubstring(s, pattern) > 0
{
  if |s| < |pattern| {
  } else if s[..|pattern|] == pattern {
  } else {
    FindIndexCountSubstring(s[1..], pattern);
  }
}

lemma CountSubstringPositiveImpliesFindIndexNonNegative(s: string, pattern: string)
  requires |pattern| > 0
  ensures CountSubstring(s, pattern) > 0 ==> FindIndex(s, pattern) >= 0
{
  FindIndexCountSubstring(s, pattern);
}

lemma FindIndexNonNegativeImpliesCountSubstringPositive(s: string, pattern: string)
  requires |pattern| > 0
  ensures FindIndex(s, pattern) >= 0 ==> CountSubstring(s, pattern) > 0
{
  FindIndexCountSubstring(s, pattern);
}

lemma CountSubstringZeroImpliesFindIndexNegative(s: string, pattern: string)
  requires |pattern| > 0
  ensures CountSubstring(s, pattern) == 0 ==> FindIndex(s, pattern) == -1
{
  FindIndexCountSubstring(s, pattern);
}

lemma FindIndexNegativeImpliesCountSubstringZero(s: string, pattern: string)
  requires |pattern| > 0
  ensures FindIndex(s, pattern) == -1 ==> CountSubstring(s, pattern) == 0
{
  FindIndexCountSubstring(s, pattern);
}

lemma FindIndexImpliesSubstring(s: string, pattern: string, index: int)
  requires |pattern| > 0 && index >= 0 && index <= |s| - |pattern|
  ensures FindIndex(s[index..], pattern) >= 0 <==> CountSubstring(s[index..], pattern) > 0
{
  FindIndexCountSubstring(s[index..], pattern);
}

lemma CountSubstringTail(s: string, pattern: string)
  requires |pattern| > 0
  ensures CountSubstring(s, pattern) > 0 ==> CountSubstring(s[1..], pattern) > 0 || s[..|pattern|] == pattern
{
}

lemma FindIndexTail(s: string, pattern: string)
  requires |pattern| > 0
  ensures FindIndex(s, pattern) >= 0 ==> FindIndex(s[1..], pattern) >= 0 || s[..|pattern|] == pattern
{
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
  
  var hasAB := CountSubstring(s, "AB") > 0;
  var hasBA := CountSubstring(s, "BA") > 0;
  
  if !hasAB || !hasBA {
    result := "NO";
    return;
  }
  
  var abIndex := FindIndex(s, "AB");
  var baIndex := FindIndex(s, "BA");
  
  if abIndex >= 0 && abIndex + 2 < |s| {
    var afterAB := s[abIndex + 2..];
    if CountSubstring(afterAB, "BA") > 0 {
      result := "YES";
      return;
    }
  }
  
  if baIndex >= 0 && baIndex + 2 < |s| {
    var afterBA := s[baIndex + 2..];
    if CountSubstring(afterBA, "AB") > 0 {
      result := "YES";
      return;
    }
  }
  
  result := "NO";
}
// </vc-code>

