// <vc-preamble>
function abs(x: real): real
{
  if x < 0.0 then -x else x
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method has_close_elements(numbers: seq<real>, threshold: real) returns (result: bool)
    ensures result <==> exists i, j ::
      0 <= i < |numbers| &&
      0 <= j < |numbers| &&
      i != j &&
      abs(numbers[i] - numbers[j]) < threshold
    ensures result ==> |numbers| > 1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added loop invariants to prove postconditions */
  result := false;
  var n := |numbers|;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant !result ==> forall k, l :: (0 <= k < i && k < l < |numbers|) ==> abs(numbers[k] - numbers[l]) >= threshold
  {
    var j := i + 1;
    while j < n
      invariant i < n
      invariant i < j <= n
      invariant !result ==> forall k, l :: (0 <= k < i && k < l < |numbers|) ==> abs(numbers[k] - numbers[l]) >= threshold
      invariant !result ==> forall l :: i < l < j ==> abs(numbers[i] - numbers[l]) >= threshold
    {
      if abs(numbers[i] - numbers[j]) < threshold {
        result := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
