

// <vc-helpers>
predicate is_prime(k: int) {
  k > 1 && forall i :: 2 <= i < k ==> k % i != 0
}

function filter_primes(lst: seq<int>): (primes: seq<int>)
  ensures forall i :: 0 <= i < |primes| ==> is_prime(primes[i])
  ensures forall i :: 0 <= i < |lst| && is_prime(lst[i]) ==> lst[i] in primes
{
  if |lst| == 0 then
    []
  else
    var tail := filter_primes(lst[1..]);
    if is_prime(lst[0]) then
      [lst[0]] + tail
    else
      tail
}

function max_seq(lst: seq<int>): (max: int)
  requires |lst| > 0
  ensures forall i :: 0 <= i < |lst| ==> lst[i] <= max
  ensures max in lst
{
  if |lst| == 1 then
    lst[0]
  else
    var suf := max_seq(lst[1..]);
    if lst[0] > suf then lst[0] else suf
}

function digits_sum(x: nat): nat 
  decreases x
{
  if x < 10 then x else (x % 10) + digits_sum(x / 10)
}

function max_value(a: int, b: int): int {
  if a > b then a else b
}

lemma max_in_lemma(lst: seq<int>)
  requires |lst| > 0
  ensures max_seq(lst) in lst
{
}

lemma max_seq_lemma(lst: seq<int>, sub: seq<int>)
  requires |lst| > 0 && sub == filter_primes(lst)
  requires |sub| > 0
  ensures max_seq(sub) == max_seq(filter_primes(lst))
{
}

lemma filter_primes_contains_all(lst: seq<int>)
  ensures forall x :: x in lst && is_prime(x) ==> x in filter_primes(lst)
{
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
  assert |primes| > 0;
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