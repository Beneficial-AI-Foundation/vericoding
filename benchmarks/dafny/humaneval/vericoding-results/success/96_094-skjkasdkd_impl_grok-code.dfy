// <vc-preamble>
function digits_sum(x: nat): nat {
  if x == 0 then 0 else x % 10 + digits_sum(x / 10)
}
function max_seq(lst: seq<int>): (max: int)

  requires |lst| > 0

  ensures forall i :: 0 <= i < |lst| ==> lst[i] <= max

{

  if |lst| == 1
    then lst[0]
    else
      var suf := max_seq(lst[1..]);
      max(lst[0], suf)

}
function filter_primes(lst: seq<int>): (primes: seq<int>)

  ensures forall i :: 0 <= i < |primes| ==> is_prime(primes[i])
  ensures forall i :: 0 <= i < |lst| && is_prime(lst[i]) ==> lst[i] in primes

{

  if |lst| == 0
    then []
    else
      var tail := filter_primes(lst[1..]);
      (if is_prime(lst[0]) then [lst[0]] else []) + tail

}
function max(a: int, b: int): int
  ensures max(a, b) == a || max(a, b) == b
  ensures max(a, b) >= a && max(a, b) >= b
{
  if a > b then a else b
}
function is_prime(k: int) : bool {
  k != 1 && forall i :: 2 <= i < k ==> k % i != 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method skjkasdkd(lst: seq<nat>) returns (dsum: nat)

  requires exists i :: 0 <= i < |lst| && is_prime(lst[i])

  ensures dsum == digits_sum(max_seq(filter_primes(lst)))
// </vc-spec>
// <vc-code>
{
  var primes := filter_primes(lst);
  var m := max_seq(primes);
  dsum := digits_sum(m);
}
// </vc-code>
