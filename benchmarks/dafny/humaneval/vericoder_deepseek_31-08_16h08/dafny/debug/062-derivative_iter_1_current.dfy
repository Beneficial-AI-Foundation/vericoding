

// <vc-helpers>
lemma FactLemma(n: nat)
  ensures n * (n+1) / 2 == (|seq(n, i => i)| * (|seq(n, i => i)| - 1)) / 2
{
  // This lemma helps with arithmetic properties needed for verification
}
// </vc-helpers>

// <vc-spec>
method derivative(xs: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires |xs| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == |xs| - 1
  ensures forall i :: 0 <= i < |result| ==> result[i] == xs[i+1] * (i+1)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  result := seq(|xs| - 1, i requires 0 <= i < |xs| - 1 => xs[i+1] * (i+1));
}
// </vc-code>

