method is_prime(k: int) returns (result: bool)
  // pre-conditions-start
  requires k >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result ==> exists j :: 2 <= j < k && k % j == 0
  // post-conditions-end
{
  // impl-start
  var i := 2;
  result := true;
  while i < k
    // invariants-start
    invariant 2 <= i <= k
    invariant !result ==> exists j :: 2 <= j < i && k % j == 0
    invariant result ==> forall j :: 2 <= j < i ==> k % j != 0
    // invariants-end
  {
    if k % i == 0 {
      result := false;
    }
    i := i + 1;
  }
  // impl-end
}

function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}
// pure-end
method largest_prime_factor(n: int) returns (largest: int)
  // pre-conditions-start
  requires n >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures 1 <= largest <= n && (largest == 1 || (largest > 1 && is_prime_pred(largest)))
  // post-conditions-end
{
  // impl-start
  largest := 1;
  var j := 2;
  while j <= n
    // invariants-start
    invariant 2 <= j <= n + 1
    invariant 1 <= largest < j
    invariant largest == 1 || (largest > 1 && is_prime_pred(largest))
    // invariants-end
  {
    var flag := is_prime(j);
    if n % j == 0 && flag {
      largest := if largest > j then largest else j;
    }
    j := j + 1;
  }
  // impl-end
}
