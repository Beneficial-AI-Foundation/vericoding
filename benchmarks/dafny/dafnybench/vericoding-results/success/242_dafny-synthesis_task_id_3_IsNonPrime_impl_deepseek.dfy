

// <vc-helpers>
lemma HasDivisorInRange(n: int, start: int, end: int) returns (divisor: int)
  requires n >= 2
  requires 2 <= start <= end <= n
  ensures (2 <= divisor < n && n % divisor == 0) || divisor == -1
  ensures (exists k :: start <= k < end && n % k == 0) ==> divisor != -1
  decreases end - start
{
  if start >= end {
    divisor := -1;
  } else if n % start == 0 {
    divisor := start;
  } else {
    divisor := HasDivisorInRange(n, start + 1, end);
  }
}
// </vc-helpers>

// <vc-spec>
method IsNonPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result <==> (exists k :: 2 <= k < n && n % k == 0)
// </vc-spec>
// <vc-code>
{
  var found := false;
  var k := 2;
  while k < n
    invariant 2 <= k <= n
    invariant !found ==> forall j :: 2 <= j < k ==> n % j != 0
    invariant found ==> exists j :: 2 <= j < n && n % j == 0
    decreases n - k
  {
    if n % k == 0 {
      found := true;
    }
    k := k + 1;
  }
  result := found;
}
// </vc-code>

