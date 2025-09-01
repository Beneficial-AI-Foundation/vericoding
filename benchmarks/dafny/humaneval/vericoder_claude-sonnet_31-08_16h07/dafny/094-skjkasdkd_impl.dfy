

// <vc-helpers>
lemma filter_primes_preserves_existence(lst: seq<nat>)
  requires exists i :: 0 <= i < |lst| && is_prime(lst[i])
  ensures |filter_primes(lst)| > 0
{
  if |lst| == 1 {
    assert is_prime(lst[0]);
    assert filter_primes(lst) == [lst[0]];
  } else {
    if is_prime(lst[0]) {
      assert filter_primes(lst) == [lst[0]] + filter_primes(lst[1..]);
      assert |filter_primes(lst)| >= 1;
    } else {
      assert exists i :: 1 <= i < |lst| && is_prime(lst[i]);
      assert exists j :: 0 <= j < |lst[1..]| && is_prime(lst[1..][j]);
      filter_primes_preserves_existence(lst[1..]);
      assert |filter_primes(lst[1..])| > 0;
      assert filter_primes(lst) == filter_primes(lst[1..]);
      assert |filter_primes(lst)| > 0;
    }
  }
}

lemma filter_primes_subset_conversion(lst: seq<nat>) 
  ensures forall i :: 0 <= i < |filter_primes(lst)| ==> filter_primes(lst)[i] >= 0
{
  if |lst| == 0 {
  } else {
    filter_primes_subset_conversion(lst[1..]);
    if is_prime(lst[0]) {
      assert lst[0] >= 0;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method skjkasdkd(lst: seq<nat>) returns (dsum: nat)
  // pre-conditions-start
  requires exists i :: 0 <= i < |lst| && is_prime(lst[i])
  // pre-conditions-end
  // post-conditions-start
  ensures dsum == digits_sum(max_seq(filter_primes(lst)))
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  filter_primes_preserves_existence(lst);
  var primes := filter_primes(lst);
  filter_primes_subset_conversion(lst);
  var max_prime := max_seq(primes);
  dsum := digits_sum(max_prime);
}
// </vc-code>

function digits_sum(x: nat): nat {
  if x == 0 then 0 else x % 10 + digits_sum(x / 10)
}
// pure-end
function max_seq(lst: seq<int>): (max: int)
  // pre-conditions-start
  requires |lst| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |lst| ==> lst[i] <= max
  // post-conditions-end
{
  // impl-start
  if |lst| == 1
    then lst[0]
    else
      var suf := max_seq(lst[1..]);
      max(lst[0], suf)
  // impl-end
}
function filter_primes(lst: seq<int>): (primes: seq<int>)
  // post-conditions-start
  ensures forall i :: 0 <= i < |primes| ==> is_prime(primes[i])
  ensures forall i :: 0 <= i < |lst| && is_prime(lst[i]) ==> lst[i] in primes
  // post-conditions-end
{
  // impl-start
  if |lst| == 0
    then []
    else
      var tail := filter_primes(lst[1..]);
      (if is_prime(lst[0]) then [lst[0]] else []) + tail
  // impl-end
}
// pure-end
function max(a: int, b: int): int
  ensures max(a, b) == a || max(a, b) == b
  ensures max(a, b) >= a && max(a, b) >= b
{
  if a > b then a else b
}
// pure-end
function is_prime(k: int) : bool {
  k != 1 && forall i :: 2 <= i < k ==> k % i != 0
}
// pure-end