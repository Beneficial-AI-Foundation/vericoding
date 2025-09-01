

// <vc-helpers>
function digits_sum(x: nat): nat {
  if x == 0 then 0 else x % 10 + digits_sum(x / 10)
}

function max_seq_int(lst: seq<int>): (max: int)
  requires |lst| > 0
  ensures forall i :: 0 <= i < |lst| ==> lst[i] <= max
{
  if |lst| == 1 then lst[0]
  else
    var suf := max_seq_int(lst[1..]);
    max_int(lst[0], suf)
}

function filter_primes_nat(lst: seq<nat>): (primes: seq<nat>)
  ensures forall i :: 0 <= i < |primes| ==> is_prime(primes[i])
  ensures forall i :: 0 <= i < |lst| && is_prime(lst[i]) ==> lst[i] in primes
{
  if |lst| == 0 then []
  else
    var tail := filter_primes_nat(lst[1..]);
    (if is_prime(lst[0]) then [lst[0]] else []) + tail
}

function max_int(a: int, b: int): int
  ensures max_int(a, b) == a || max_int(a, b) == b
  ensures max_int(a, b) >= a && max_int(a, b) >= b
{
  if a > b then a else b
}

function is_prime(k: nat) : bool {
  k >= 2 && forall i :: 2 <= i * i <= k ==> k % i != 0
}

function seq_of<A, B>(s: seq<A>, f: A -> B): seq<B>
  ensures |seq_of(s, f)| == |s|
  ensures forall i :: 0 <= i < |s| ==> seq_of(s, f)[i] == f(s[i])
{
  if |s| == 0 then []
  else [f(s[0])] + seq_of(s[1..], f)
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
  var filtered: seq<nat> := filter_primes_nat(lst);
  assert |filtered| > 0 by {
    var i : int := 0;
    while i < |lst|
      invariant 0 <= i <= |lst|
      invariant exists j :: 0 <= j < i && is_prime(lst[j]) ==> exists k :: 0 <= k < |filtered| && filtered[k] == lst[j]
    {
      if is_prime(lst[i]) {
        assert exists j :: 0 <= j < |filtered| && filtered[j] == lst[i];
        break; 
      }
      i := i + 1;
    }
  }
  var filtered_to_int: seq<int> := seq_of(filtered, (x:nat) => x as int);
  var max_val: int := max_seq_int(filtered_to_int);
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