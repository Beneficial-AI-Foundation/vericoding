

// <vc-helpers>
lemma filtered_primes_are_nonnegative(lst: seq<nat>)
  ensures forall i :: 0 <= i < |filter_primes(lst)| ==> filter_primes(lst)[i] >= 0
{
  if |lst| == 0 {
  } else {
    filtered_primes_are_nonnegative(lst[1..]);
    var tail := filter_primes(lst[1..]);
    if is_prime(lst[0]) {
      // The first element is lst[0] (which is nat, so >=0) and the tail is nonnegative by induction.
    } else {
      // The result is tail, which is nonnegative by induction.
    }
  }
}

lemma nonnegative_seq_max_nonnegative(lst: seq<int>)
  requires forall i :: 0 <= i < |lst| ==> lst[i] >= 0
  requires |lst| > 0
  ensures max_seq(lst) >= 0
{
  if |lst| == 1 {
  } else {
    var suf := max_seq(lst[1..]);
    nonnegative_seq_max_nonnegative(lst[1..]);
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
  var primes := filter_primes(lst);
  filtered_primes_are_nonnegative(lst);
  nonnegative_seq_max_nonnegative(primes);
  var max_prime := max_seq(primes);
  dsum := digits_sum(max_prime as nat);
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