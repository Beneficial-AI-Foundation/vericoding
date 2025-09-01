

// <vc-helpers>
function digits_sum(x: nat): nat {
  if x == 0 then 0 else x % 10 + digits_sum(x / 10)
}

function max_seq(lst: seq<nat>): (max: nat)
  requires |lst| > 0
  ensures forall i :: 0 <= i < |lst| ==> lst[i] <= max
  ensures exists i :: 0 <= i < |lst| && lst[i] == max
{
  if |lst| == 1
    then lst[0]
    else
      var suf := max_seq(lst[1..]);
      if lst[0] > suf then lst[0] else suf
}

function filter_primes(lst: seq<nat>): (primes: seq<nat>)
  ensures forall i :: 0 <= i < |primes| ==> is_prime(primes[i])
  ensures forall i :: 0 <= i < |lst| && is_prime(lst[i]) ==> lst[i] in primes
  ensures forall p :: p in primes ==> p in lst
{
  if |lst| == 0
    then []
    else
      var tail := filter_primes(lst[1..]);
      (if is_prime(lst[0]) then [lst[0]] else []) + tail
}

function is_prime(k: nat) : bool {
  k > 1 && forall i :: 2 <= i * i <= k ==> k % i != 0
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
  var filtered := filter_primes(lst);
  assert |filtered| > 0
    by {
      var i := 0;
      var found_prime := false;
      while i < |lst|
        invariant 0 <= i <= |lst|
        invariant !found_prime ==> (forall j :: 0 <= j < i ==> !is_prime(lst[j]))
      {
        if is_prime(lst[i]) {
          found_prime := true;
          // This assertion is required to make the post-condition provable
          // It asserts that if a prime is found in `lst`, it will be in `filtered`
          assert lst[i] in filtered;
          break;
        }
        i := i + 1;
      }
      assert found_prime; // This comes from the pre-condition of skjkasdkd
      // Now, we need to show that if a prime was found in `lst`, then `filtered` is not empty.
      // Since `lst[i]` is in `filtered` and `lst[i]` is a prime, `filtered` cannot be empty.
      assert |filtered| > 0;
    }

  var maxValue := max_seq(filtered);
  dsum := digits_sum(maxValue);
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