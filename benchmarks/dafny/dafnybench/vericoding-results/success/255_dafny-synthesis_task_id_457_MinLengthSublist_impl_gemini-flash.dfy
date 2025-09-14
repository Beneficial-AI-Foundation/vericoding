

// <vc-helpers>
lemma MinLengthSublistLemma(s: seq<seq<int>>, minSublist: seq<int>)
    requires |s| > 0
    requires minSublist in s
    requires forall sublist :: sublist in s ==> |minSublist| <= |sublist|
    ensures true
{
    // This lemma doesn't require a specific proof, as its purpose is to
    // demonstrate the properties of minSublist, which are already part of the
    // postconditions of the MinLengthSublist method.
    // However, if there were complex inductive proofs or properties to derive
    // from this, this is where it would go.
}
// </vc-helpers>

// <vc-spec>
method MinLengthSublist(s: seq<seq<int>>) returns (minSublist: seq<int>)
    requires |s| > 0
    ensures minSublist in s
    ensures forall sublist :: sublist in s ==> |minSublist| <= |sublist|
// </vc-spec>
// <vc-code>
{
  var minLength := |s[0]|;
  var minIndex := 0;

  var i := 1;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= minIndex < i
    invariant minLength == |s[minIndex]|
    invariant forall j :: 0 <= j < i ==> |s[minIndex]| <= |s[j]|
  {
    if |s[i]| < minLength {
      minLength := |s[i]|;
      minIndex := i;
    }
    i := i + 1;
  }
  minSublist := s[minIndex];
}
// </vc-code>

