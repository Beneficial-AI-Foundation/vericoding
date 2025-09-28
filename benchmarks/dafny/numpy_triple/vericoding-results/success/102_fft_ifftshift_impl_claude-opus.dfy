// <vc-preamble>
// Method to perform inverse FFT shift on a sequence of real numbers
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ifftshift(x: seq<real>) returns (result: seq<real>)
  requires |x| > 0
  ensures |result| == |x|
  ensures forall i :: 0 <= i < |x| ==> 
    result[i] == x[(i + |x| / 2) % |x|]
// </vc-spec>
// <vc-code>
{
  var n := |x|;
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == x[(j + n / 2) % n]
  {
    result := result + [x[(i + n / 2) % n]];
    i := i + 1;
  }
}
// </vc-code>
