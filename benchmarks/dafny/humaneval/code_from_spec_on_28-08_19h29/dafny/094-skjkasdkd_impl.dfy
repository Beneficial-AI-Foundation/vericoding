// <vc-helpers>
function digits_sum_unique(x: nat): nat {
  if x == 0 then 0 else x % 10 + digits_sum_unique(x / 10)
}

function max_seq_unique(lst: seq<int>): (max: int)
  requires |lst| > 0
  ensures forall i :: 0 <= i < |lst| ==> lst[i] <= max
{
  if |lst| == 1
    then lst[0]
    else
      var suf := max_seq_unique(lst[1..]);
      max_unique(lst[0], suf)
}

function filter_primes_unique(lst: seq<int>): (primes: seq<int>)
  ensures forall i :: 0 <= i < |primes| ==> is_prime_unique(primes[i])
  ensures forall i :: 0 <= i < |lst| && is_prime_unique(lst[i]) ==> lst[i] in primes
{
  if |lst| == 0
    then []
    else
      var tail := filter_primes_unique(lst[1..]);
      (if is_prime_unique(lst[0]) then [lst[0]] else []) + tail
}

function max_unique(a: int, b: int): int
  ensures max_unique(a, b) == a || max_unique(a, b) == b
  ensures max_unique(a, b) >= a && max_unique(a, b) >= b
{
  if a > b then a else b
}

function is_prime_unique(k: int): bool {
  k != 1 && forall i :: 2 <= i < k ==> k % i != 0
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def sum_largest_prime(lst : list[int]) -> int
You are given a list of integers. You need to find the largest prime value and return the sum of its digits. Note(George): Modified to use List of nats because all examples are nats.
*/
// </vc-description>

// <vc-spec>
method sum_largest_prime(lst: seq<int>) returns (result: int)
  requires |lst| > 0
  requires forall i :: 0 <= i < |lst| ==> lst[i] >= 0
  ensures result >= 0
  ensures var primes := filter_primes_unique(lst);
          if |primes| == 0 then result == 0
          else result == digits_sum_unique(max_seq_unique(primes))
// </vc-spec>
// <vc-code>
{
  var primes := filter_primes_unique(lst);
  if |primes| == 0 {
    result := 0;
  } else {
    var largest_prime := max_seq_unique(primes);
    result := digits_sum_unique(largest_prime);
  }
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