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
lemma FindIndexImpliesCountPositive(s: string, pattern: string)
  requires |pattern| > 0
  decreases |s|
  ensures FindIndex(s,pattern) >= 0 ==> CountSubstring(s,pattern) > 0
{
  if |pattern| == 0 || |s| < |pattern| {
    // antecedent impossible, nothing to prove
  } else if s[..|pattern|] == pattern {
    if FindIndex(s,pattern) >= 0 {
      // By definition CountSubstring returns 1 + CountSubstring(s[1..], pattern)
      assert CountSubstring(s,pattern) == 1 + CountSubstring(s[1..], pattern);
      assert CountSubstring(s,pattern) > 0;
    }
  } else {
    var rest := FindIndex(s[1..], pattern);
    if rest >= 0 {
      // By definition FindIndex(s, pattern) = 1 + rest, and by induction CountSubstring(s[1..],pattern) > 0
      FindIndexImpliesCountPositive(s[1..], pattern);
      assert CountSubstring(s,pattern) == CountSubstring(s[1..], pattern);
      assert CountSubstring(s,pattern) > 0;
    }
  }
}

lemma ZeroCountImpliesFindIndexNegative(s: string, pattern: string)
  requires |pattern| > 0
  decreases |s|
  ensures CountSubstring(s,pattern) == 0 ==> FindIndex(s,pattern) < 0
{
  if CountSubstring(s,pattern) == 0 {
    if FindIndex(s,pattern) >= 0 {
      FindIndexImpliesCountPositive(s,pattern);
      // From the lemma we obtain CountSubstring(s,pattern) > 0, contradiction.
      assert false;
    }
    // Thus FindIndex(s,pattern) < 0
  }
}

lemma NoNonOverlapIfNoABorBA(s: string)
  ensures CountSubstring(s,"AB") == 0 || CountSubstring(s,"BA") == 0 ==> !HasNonOverlappingABAndBA(s)
{
  if CountSubstring(s,"AB") == 0 {
    ZeroCountImpliesFindIndexNegative(s, "AB");
    assert FindIndex(s,"AB") < 0;
  } else if CountSubstring(s,"BA") == 0 {
    ZeroCountImpliesFindIndexNegative(s, "BA");
    assert FindIndex(s,"BA") < 0;
  }

  if CountSubstring(s,"AB") == 0 || CountSubstring(s,"BA") == 0 {
    // HasNonOverlappingABAndBA requires both indices >= 0, so it cannot hold
    assert !(FindIndex(s,"AB") >= 0 && FindIndex(s,"BA") >= 0);
    assert !((FindIndex(s,"AB") >= 0 && FindIndex(s,"BA") >= 0) &&
            ((FindIndex(s,"AB") >= 0 && FindIndex(s,"AB") + 2 < |s| && CountSubstring(s[FindIndex(s,"AB") + 2..], "BA") > 0) ||
             (FindIndex(s,"BA") >= 0 && FindIndex(s,"BA") + 2 < |s| && CountSubstring(s[FindIndex(s,"BA") + 2..], "AB") > 0)));
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
  // Provide the lemma fact to the verifier
  NoNonOverlapIfNoABorBA(s);
  if HasNonOverlappingABAndBA(s) {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>

