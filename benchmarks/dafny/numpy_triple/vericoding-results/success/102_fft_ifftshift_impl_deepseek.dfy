// <vc-preamble>
// Method to perform inverse FFT shift on a sequence of real numbers
// </vc-preamble>

// <vc-helpers>
function mod(a: int, b: int): int requires b > 0 { a % b }
/* helper modified by LLM (iteration 3): kept mod helper for clarity */
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
  /* code modified by LLM (iteration 3): fixed seq/array assignment by using sequence construction */
  var n := |x|;
  var half := n / 2;
  var temp: seq<real> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |temp| == i
    invariant forall j :: 0 <= j < i ==> temp[j] == x[(j + half) % n]
  {
    temp := temp + [x[(i + half) % n]];
    i := i + 1;
  }
  result := temp;
}
// </vc-code>
