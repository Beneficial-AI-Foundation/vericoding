function Power(base: int, exponent: int): int
    requires exponent >= 0
{
    if exponent == 0 then 1
    else base * Power(base, exponent-1)
}

// <vc-helpers>
// Helper lemma to ensure Power function properties if needed
lemma PowerNonNegative(base: int, exponent: int)
  requires exponent >= 0
  ensures Power(base, exponent) >= 0 || base < 0
{
  if exponent == 0 {
    // Base case: Power(base, 0) = 1 >= 0
  } else {
    // Recursive case handled by Dafny's definition
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method PowerOfListElements(l: seq<int>, n: int) returns (result: seq<int>)
    requires n >= 0
    ensures |result| == |l|
    ensures forall i :: 0 <= i < |l| ==> result[i] == Power(l[i], n)
// </vc-spec>
// </vc-spec>

// <vc-code>
method PowerOfListElementsImpl(l: seq<int>, n: int) returns (result: seq<int>)
  requires n >= 0
  ensures |result| == |l|
  ensures forall i :: 0 <= i < |l| ==> result[i] == Power(l[i], n)
{
  result := [];
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == Power(l[k], n)
  {
    result := result + [Power(l[i], n)];
    i := i + 1;
  }
}
// </vc-code>
