

// <vc-helpers>
predicate is_prime(k: int) {
  k != 1 && forall i :: 2 <= i < k ==> k % i != 0
}

function method filter_primes(lst: seq<int>): (primes: seq<int>)
  ensures forall i :: 0 <= i < |primes| ==> is_prime(primes[i])
  ensures forall i :: 0 <= i < |lst| && is_prime(lst[i]) ==> lst[i] in primes
{
  if |lst| == 0 then
    []
  else
    var tail := filter_primes(lst[1..]);
    (if is_prime(lst[0]) then [lst[0]] else []) + tail
}

function method max_seq(lst: seq<int>): (max: int)
  requires |lst| > 0
  ensures forall i :: 0 <= i < |lst| ==> lst[i] <= max
{
  if |lst| == 1 then
    lst[0]
  else
    var suf := max_seq(lst[1..]);
    if lst[0] > suf then lst[0] else suf
}

function method digits_sum(x: nat): nat {
  if x < 10 then x else (x % 10) + digits_sum(x / 10)
}

lemma max_lemma(a: int, b: int)
  ensures max(a, b) == a || max(a, b) == b
  ensures max(a, b) >= a && max(a, b) >= b
{
}

function method max(a: int, b: int): int {
  if a > b then a else b
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
  var max_prime := 0;
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant i == 0 ==> max_prime == 0
    invariant i > 0 ==> (exists j :: 0 <= j < i && is_prime(lst[j])) ==> max_prime == max_seq(filter_primes(lst[..i]))
    invariant i > 0 ==> max_prime >= max_seq(filter_primes(lst[..i]))
  {
    if is_prime(lst[i]) && max_prime < lst[i] {
      max_prime := lst[i];
    }
    i := i + 1;
  }
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