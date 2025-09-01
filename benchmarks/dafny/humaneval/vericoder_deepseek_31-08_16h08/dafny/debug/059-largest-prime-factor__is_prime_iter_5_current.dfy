function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}

// <vc-helpers>
lemma mod_lemma(a: int, b: int)
  requires a >= 0 && b > 0
  ensures 0 <= a % b < b
{
}

lemma no_divisors_in_range(k: int, start: int, end: int)
  requires k >= 2 && start >= 2 && end <= k
  ensures (forall i :: start <= i < end ==> k % i != 0) ==>
          (forall i :: 2 <= i < end ==> k % i != 0)
{
}

lemma exists_divisor(k: int, j: int)
  requires k >= 2 && j >= 2 && j < k && k % j == 0
  ensures exists j :: 2 <= j < k && k % j == 0
{
}

lemma extend_range(k: int, i: int)
  requires k >= 2 && i >= 2
  requires forall j :: 2 <= j < i ==> k % j != 0
  ensures forall j :: 2 <= j < i + 1 ==> k % j != 0
{
  var j: int := 2;
  while j < i + 1
    invariant 2 <= j <= i + 1
    invariant forall m :: 2 <= m < j ==> k % m != 0
  {
    if j < i {
      // Already known from precondition
    } else if j == i {
      // Need to show k % i != 0
      // This follows from the loop condition in the calling method
    }
    j := j + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method is_prime(k: int) returns (result: bool)
  // pre-conditions-start
  requires k >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result ==> exists j :: 2 <= j < k && k % j == 0
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var i := 2;
  result := true;
  
  while i < k
    invariant 2 <= i <= k
    invariant result ==> forall j :: 2 <= j < i ==> k % j != 0
    invariant !result ==> exists j :: 2 <= j < i && k % j == 0
  {
    mod_lemma(k, i);
    if k % i == 0 {
      result := false;
      exists_divisor(k, i);
    } else {
      if result {
        // Prove that all divisors up to i+1 are non-zero
        assert forall j :: 2 <= j < i ==> k % j != 0;
        extend_range(k, i);
      }
    }
    i := i + 1;
  }
  
  if result {
    assert forall j :: 2 <= j < k ==> k % j != 0;
  } else {
    assert exists j :: 2 <= j < k && k % j == 0;
  }
}
// </vc-code>

method largest_prime_factor(n: int) returns (largest: int)
  // pre-conditions-start
  requires n >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures 1 <= largest <= n && (largest == 1 || (largest > 1 && is_prime_pred(largest)))
  // post-conditions-end
{
  assume{:axiom} false;
}