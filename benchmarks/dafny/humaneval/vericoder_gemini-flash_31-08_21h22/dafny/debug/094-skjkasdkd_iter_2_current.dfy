

// <vc-helpers>
function digits_sum(x: nat): nat {
  if x == 0 then 0 else x % 10 + digits_sum(x / 10)
}

function max_seq(lst: seq<int>): (max: int)
  requires |lst| > 0
  ensures forall i :: 0 <= i < |lst| ==> lst[i] <= max
{
  if |lst| == 1 then lst[0]
  else
    var suf := max_seq(lst[1..]);
    max(lst[0], suf)
}

function filter_primes(lst: seq<nat>): (primes: seq<nat>)
  ensures forall i :: 0 <= i < |primes| ==> is_prime(primes[i])
  ensures forall i :: 0 <= i < |lst| && is_prime(lst[i]) ==> lst[i] in primes
{
  if |lst| == 0 then []
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
  k != 1 && k >= 2 && forall i :: 2 <= i * i <= k ==> k % i != 0
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
  var filtered: seq<nat> := filter_primes(lst);
  assert |filtered| > 0 by {
    var i : int := 0;
    while i < |lst|
      invariant 0 <= i <= |lst|
    {
      if is_prime(lst[i]) {
        assert exists j :: 0 <= j < |filtered| && filtered[j] == lst[i];
        break; 
      }
      i := i + 1;
    }
  }
  var max_val: int := max_seq(filtered);
  dsum := digits_sum(max_val as nat);
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