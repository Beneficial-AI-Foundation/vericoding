method skjkasdkd(lst: seq<nat>) returns (dsum: nat)
  // pre-conditions-start
  requires exists i :: 0 <= i < |lst| && is_prime(lst[i])
  // pre-conditions-end
  // post-conditions-start
  ensures dsum == digits_sum(max_seq(filter_primes(lst)))
  // post-conditions-end
{
  // impl-start
  var primes := [];
  var i := 0;
  while i < |lst|
    // invariants-start
    invariant 0 <= i <= |lst|
    invariant primes == filter_primes(lst[..i])
    // invariants-end
  {
    if is_prime(lst[i]) {
      primes := primes + [lst[i]];
    }
    // assert-start
    assert filter_primes(lst[..i + 1]) == filter_primes(lst[..i]) + (
      if is_prime(lst[i]) then [lst[i]] else []
    ) by {
      assert lst[..i+1][..i] == lst[..i];
      primes_prop(lst[..i + 1]);
    }
    // assert-end
    i := i + 1;
  }

  assert lst[..|lst|] == lst; // assert-line

  var max_prime := primes[0];
  i := 1;
  while i < |primes|
    // invariants-start
    invariant 1 <= i <= |primes|
    invariant forall j :: 0 <= j < i ==> max_prime >= primes[j]
    invariant max_prime == max_seq(primes[..i])
    // invariants-end
  {
    max_prime := max(max_prime, primes[i]);
    // assert-start
    assert max_seq(primes[..i + 1]) == max(max_seq(primes[..i]), primes[i]) by {
      assert primes[..i + 1][..i] == primes[..i];
      max_prop(primes[..i + 1]);
    }
    // assert-end
    i := i + 1;
  }

  assert primes[..|primes|] == primes; // assert-line
  assert max_prime == max_seq(primes); // assert-line

  dsum := digits_sum(max_prime);
  // impl-end
}

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

lemma max_prop(s: seq<int>)
  requires |s| > 1
  ensures max_seq(s) == max(max_seq(s[..|s| - 1]), s[|s| - 1])
{
  assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
}
// pure-end
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
lemma primes_prop(s: seq<int>)
    requires |s| > 0
    ensures filter_primes(s) == filter_primes(s[..|s| - 1]) + (
      if is_prime(s[|s| - 1]) then [s[|s| - 1]] else []
    )
{
    if (|s| > 1) {
        assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
    }
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
