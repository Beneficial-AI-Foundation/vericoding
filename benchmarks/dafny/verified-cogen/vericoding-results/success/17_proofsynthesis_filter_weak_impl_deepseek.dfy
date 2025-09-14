// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma HelperLemma(x: seq<int>) ensures |x| == 0 ==> forall k :: 0 <= k < |x| ==> x[k] % 3 == 0 && x[k] in x[..] { }
// </vc-helpers>

// <vc-spec>
method Myfun4(x: array<int>, y: array<int>) returns ()
    requires y.Length == 0
    ensures forall k :: 0 <= k < y.Length ==> y[k] % 3 == 0 && y[k] in x[..]
// </vc-spec>
// <vc-code>
{
  assert y.Length == 0;
  HelperLemma(y[..]);
}
// </vc-code>
