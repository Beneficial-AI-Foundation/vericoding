// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): returns sequence of negative elements in order */
function negativesOf(s: seq<int>): seq<int> { if |s| == 0 then [] else if s[0] < 0 then [s[0]] + negativesOf(s[1..]) else negativesOf(s[1..]) }

/* helper modified by LLM (iteration 2): proves negativesOf only contains negatives */
lemma NegativesOfOnlyNegative(s: seq<int>) ensures forall x :: x in negativesOf(s) ==> x < 0 {
  if |s| == 0 {
  } else {
    NegativesOfOnlyNegative(s[1..]);
    if s[0] < 0 {
      // s[0] is negative and all elements of negativesOf(s[1..]) are negative by induction
    }
  }
}

/* helper modified by LLM (iteration 2): proves negativesOf contains all negative elements from the input sequence */
lemma NegativesOfContainsAll(s: seq<int>) ensures forall i :: 0 <= i < |s| && s[i] < 0 ==> s[i] in negativesOf(s) {
  if |s| == 0 {
  } else {
    // For elements beyond the first, use induction on the tail
    NegativesOfContainsAll(s[1..]);
    // If the first element is negative, it is included by construction of negativesOf
    if s[0] < 0 {
    }
  }
}
// </vc-helpers>

// <vc-spec>
method FindNegativeNumbers(arr: array<int>) returns (negative_list: seq<int>)
    ensures forall x :: x in negative_list ==> x < 0
    ensures forall i :: 0 <= i < arr.Length && arr[i] < 0 ==> arr[i] in negative_list
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): compute negatives using helper and invoke lemmas to satisfy ensures */
  negative_list := negativesOf(arr[..]);
  // Help the verifier by applying the lemmas about negativesOf
  NegativesOfOnlyNegative(arr[..]);
  NegativesOfContainsAll(arr[..]);
}

// </vc-code>
