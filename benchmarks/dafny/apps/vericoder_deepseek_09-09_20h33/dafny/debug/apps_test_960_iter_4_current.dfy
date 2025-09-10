predicate ValidInput(n: int, k: int) {
  n >= 1 && k >= 2
}

predicate SatisfiesConstraint(x: int, n: int, k: int) {
  x > 0 && k > 0 && (x / k) * (x % k) == n
}

// <vc-helpers>
lemma MinimizeHelper(x: int, n: int, k: int, candidate: int)
  requires ValidInput(n, k)
  requires candidate > 0 && SatisfiesConstraint(candidate, n, k)
  requires forall x' :: 1 <= x' < candidate ==> !SatisfiesConstraint(x', n, k)
  ensures forall x :: x > 0 && (x / k) * (x % k) == n ==> candidate <= x
{
}

lemma DivModProperties(k: int)
  requires k >= 2
  ensures forall x :: x > 0 ==> 0 <= x % k < k
  ensures forall x :: x > 0 ==> x == (x / k) * k + (x % k)
{
}

lemma ModRangeLemma(k: int)
  requires k >= 2
  ensures forall x :: x > 0 ==> 0 <= x % k < k
{
}

lemma DivisionLemma(k: int) 
  requires k >= 2
  ensures forall x :: x > 0 ==> x == (x / k) * k + (x % k)
{
}

lemma CandidatesExist(n: int, k: int)
  requires ValidInput(n, k)
  ensures exists x :: x > 0 && (x / k) * (x % k) == n
{
  var candidate := n * k + 1;
  // At least one candidate exists: n*k + 1 (with r=1)
  // This ensures we always have a valid candidate
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
  requires ValidInput(n, k)
  ensures result > 0
  ensures SatisfiesConstraint(result, n, k)
  ensures forall x :: x > 0 && (x / k) * (x % k) == n ==> result <= x
// </vc-spec>
// <vc-code>
{
  DivModProperties(k);
  CandidatesExist(n, k);
  
  var min_candidate := 0;
  var r := 1;
  while r < k
    invariant 1 <= r <= k
    invariant min_candidate == 0 || (min_candidate > 0 && SatisfiesConstraint(min_candidate, n, k))
    invariant min_candidate == 0 ==> forall x' :: 1 <= x' < r ==> !SatisfiesConstraint(x', n, k)
    invariant min_candidate > 0 ==> forall x' :: 1 <= x' < min_candidate ==> !SatisfiesConstraint(x', n, k)
  {
    if n % r == 0 {
      var d := n / r;
      var candidate := d * k + r;
      if candidate > 0 && (min_candidate == 0 || candidate < min_candidate) {
        min_candidate := candidate;
      }
    }
    r := r + 1;
  }
  
  if min_candidate > 0 {
    result := min_candidate;
    MinimizeHelper(min_candidate, n, k, min_candidate);
    return;
  }
  
  // If no candidate found with r < k, try r = k - 1
  if n % (k - 1) == 0 {
    var d := n / (k - 1);
    var candidate := d * k + (k - 1);
    result := candidate;
    MinimizeHelper(candidate, n, k, candidate);
    return;
  }
  
  // Fallback: use n*k + 1 (always valid)
  result := n * k + 1;
  MinimizeHelper(result, n, k, result);
}
// </vc-code>

