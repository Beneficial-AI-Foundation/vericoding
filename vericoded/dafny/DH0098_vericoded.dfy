// <vc-preamble>

predicate is_prime_number(num: int)
{
    num >= 2 && forall k :: 2 <= k < num ==> num % k != 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method count_up_to(n: int) returns (result: seq<int>)
    requires n >= 0
    ensures forall i :: 0 <= i < |result| ==> is_prime_number(result[i])
    ensures forall i :: 0 <= i < |result| ==> result[i] < n
    ensures forall p :: 2 <= p < n && is_prime_number(p) ==> p in result
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): handle n < 2 case to fix loop invariant entry */
  result := [];
  if n < 2 {
    return;
  }
  var i := 2;
  while i < n
    invariant 2 <= i <= n
    invariant forall k :: 0 <= k < |result| ==> is_prime_number(result[k])
    invariant forall k :: 0 <= k < |result| ==> result[k] < i
    invariant forall p :: 2 <= p < i && is_prime_number(p) ==> p in result
    invariant forall k, j :: 0 <= k < j < |result| ==> result[k] < result[j]
    invariant |result| > 0 ==> result[|result|-1] < i
  {
    var is_prime := true;
    var j := 2;
    while j < i
      invariant 2 <= j <= i
      invariant is_prime <==> forall k :: 2 <= k < j ==> i % k != 0
    {
      if i % j == 0 {
        is_prime := false;
        break;
      }
      j := j + 1;
    }
    if is_prime {
      result := result + [i];
    }
    i := i + 1;
  }
}
// </vc-code>
