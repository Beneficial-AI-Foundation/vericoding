// <vc-preamble>

predicate is_prime_number(num: int)
{
    num >= 2 && forall k :: 2 <= k < num ==> num % k != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): primality test implemented as a method */
method is_prime_test(n: int) returns (res: bool)
  requires n >= 0
  ensures res <==> is_prime_number(n)
{
  if n < 2 {
    res := false;
    return;
  }
  var k := 2;
  var ok := true;
  while k < n
    invariant 2 <= k <= n
    invariant ok ==> forall t :: 2 <= t < k ==> n % t != 0
    invariant !ok ==> exists t :: 2 <= t < k && n % t == 0
    decreases n - k
  {
    if n % k == 0 {
      ok := false;
      break;
    }
    k := k + 1;
  }
  res := ok;
}
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
  /* code modified by LLM (iteration 2): call is_prime_test via assignment to avoid using method in expression */
  result := [];
  var i := 2;
  while i < n
    invariant forall idx :: 0 <= idx < |result| ==> is_prime_number(result[idx])
    invariant forall idx :: 0 <= idx < |result| ==> result[idx] < n
    invariant forall idx :: 0 <= idx < |result| ==> result[idx] < i
    invariant forall p :: 2 <= p < i && is_prime_number(p) ==> p in result
    invariant forall i1, i2 :: 0 <= i1 < i2 < |result| ==> result[i1] < result[i2]
    decreases n - i
  {
    var prime := is_prime_test(i);
    if prime {
      result := result + [i];
    }
    i := i + 1;
  }
}
// </vc-code>
