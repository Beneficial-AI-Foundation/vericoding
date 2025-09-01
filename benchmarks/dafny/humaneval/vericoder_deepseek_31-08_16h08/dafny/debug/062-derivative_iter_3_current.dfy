

// <vc-helpers>
lemma FactLemma(n: nat)
  ensures n * (n+1) / 2 == (|seq(n, i => i)| * (|seq(n, i => i)| - 1)) / 2
{
  if n == 0 {
  } else {
    FactLemma(n-1);
  }
}

lemma SeqLenLemma(n: nat)
  ensures |seq(n, i => i)| == n
{
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
  var length := |xs| - 1;
  result := [];
  var i := 0;
  while i < length
    invariant 0 <= i <= length
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == xs[j+1] * (j+1)
  {
    result := result + [xs[i+1] * (i+1)];
    i := i + 1;
  }
}
// </vc-code>

