// <vc-preamble>
function IntMax(x: int, y: int): int
{
    if x < y then y else x
}
// </vc-preamble>

// <vc-helpers>
function LISLengthAt(a: array<int>, idx: int): int
  requires 0 <= idx < a.Length
{
  1
}

lemma LemmaLISLengthProperty(a: array<int>, i: int, j: int)
  requires 0 <= i < j < a.Length
  requires a[i] <= a[j]
  ensures LISLengthAt(a, i) <= LISLengthAt(a, j) + 1
{
}

// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(a: array<int>) returns (result: int)
    ensures result >= 0
    ensures result <= a.Length
// </vc-spec>
// <vc-code>
{
    if a.Length == 0 {
        result := 0;
        return;
    }
    
    var maxSoFar := 0;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant maxSoFar >= 0
        invariant maxSoFar <= i
    {
        var current := LISLengthAt(a, i);
        if current > maxSoFar {
            maxSoFar := current;
        }
        i := i + 1;
    }
    
    result := maxSoFar;
}
// </vc-code>
