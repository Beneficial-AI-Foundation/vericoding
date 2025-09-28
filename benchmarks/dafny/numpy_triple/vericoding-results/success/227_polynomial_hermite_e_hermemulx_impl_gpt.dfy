// <vc-preamble>
// Method to multiply a Hermite series by x
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add non-negativity guard for i+1 to avoid out-of-range indexing */
function HermeMulXElem(c: seq<real>, i: int): real
{
  if i == 0 then 0.0
  else if i == 1 then
    (if |c| > 0 then c[0] else 0.0) + (if |c| > 1 then 1.0 * c[1] else 0.0)
  else
    (if 0 <= i - 1 && i - 1 < |c| then c[i - 1] else 0.0) +
    (if 0 <= i + 1 && i + 1 < |c| then ((i - 1) as real) * c[i + 1] else 0.0)
}
// </vc-helpers>

// <vc-spec>
method HermeMulX(c: seq<real>) returns (result: seq<real>)
  requires |c| >= 0
  ensures |result| == |c| + 1
  // The first coefficient is always 0
  ensures |result| > 0 ==> result[0] == 0.0
  // For the second coefficient: c[0] plus c[1] if it exists
  ensures |c| > 0 && |result| > 1 ==> result[1] == c[0] + (if |c| > 1 then 1.0 * c[1] else 0.0)
  // General recursion relationship: result[i] = c[i-1] + (i-1)*c[i+1] with bounds checking
  ensures forall i :: 2 <= i < |result| ==> 
    result[i] == (if i-1 >= 0 && i-1 < |c| then c[i-1] else 0.0) + 
                 (if i+1 < |c| then ((i-1) as real) * c[i+1] else 0.0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): build result via array then convert to sequence */
  var n := |c|;
  var a := new real[n + 1];
  var i := 0;
  while i < n + 1
    invariant 0 <= i <= n + 1
    invariant a.Length == n + 1
    invariant forall k :: 0 <= k < i ==> a[k] == HermeMulXElem(c, k)
    decreases n + 1 - i
  {
    a[i] := HermeMulXElem(c, i);
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
