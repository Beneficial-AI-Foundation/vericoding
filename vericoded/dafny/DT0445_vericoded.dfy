// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method hermmulx(c: seq<real>) returns (result: seq<real>)
  requires |c| >= 0
  ensures |result| == |c| + 1
  ensures forall k :: 0 <= k < |result| ==>
    result[k] == 
      // Contribution from c[k-1]/2 when k > 0 and k-1 < |c|
      (if k > 0 && k-1 < |c| then c[k-1] / 2.0 else 0.0) +
      // Contribution from c[k+1]*(k+1) when k+1 < |c|
      (if k+1 < |c| then c[k+1] * (k+1) as real else 0.0)
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i <= |c|
    invariant 0 <= i <= |c| + 1
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==>
      result[k] == 
        (if k > 0 && k-1 < |c| then c[k-1] / 2.0 else 0.0) +
        (if k+1 < |c| then c[k+1] * (k+1) as real else 0.0)
  {
    var val := 0.0;
    if i > 0 && i-1 < |c| {
      val := val + c[i-1] / 2.0;
    }
    if i+1 < |c| {
      val := val + c[i+1] * (i+1) as real;
    }
    result := result + [val];
    i := i + 1;
  }
}
// </vc-code>
