// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed, it's correct */
function mod(a: int, n: int): int
  requires n > 0
  ensures 0 <= mod(a, n) < n
{
  (a % n + n) % n
}
// </vc-helpers>

// <vc-spec>
method FFTShift(x: seq<real>) returns (result: seq<real>)
  requires |x| >= 0
  ensures |result| == |x|
  // Main transformation: each element at position i comes from position (i + |x| - |x|/2) % |x|
  ensures |x| > 0 ==> forall i :: 0 <= i < |x| ==> 
    result[i] == x[(i + |x| - |x|/2) % |x|]
  // Bijective property: every input element appears exactly once in output
  ensures forall j :: 0 <= j < |x| ==> exists k :: 0 <= k < |x| && result[k] == x[j]
  // Inverse bijective property: every output element comes from exactly one input element  
  ensures forall k :: 0 <= k < |x| ==> exists j :: 0 <= j < |x| && result[k] == x[j]
  // Multiset equality: same elements with same multiplicities
  ensures multiset(result) == multiset(x)
  // Handle empty sequence case
  ensures |x| == 0 ==> result == []
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The previous error was a compilation error where `new real[n](_ => 0.0)` was being assigned to a `seq<real>` type. The fix is to use `new seq<real>(n, _ => 0.0)` to represent a sequence correctly. */
{
  var n := |x|;
  if n == 0 {
    return [];
  }
  var shifted_idx := n - n / 2;
  var res_seq: seq<real> := new seq<real>(n, _ => 0.0);
  for i := 0 to n-1
    invariant 0 <= i <= n
    invariant |res_seq| == n
    invariant forall k :: 0 <= k < i ==> res_seq[k] == x[mod(k + shifted_idx, n)]
  {
    res_seq := res_seq[i := x[mod(i + shifted_idx, n)]];
  }
  return res_seq;
}
// </vc-code>
