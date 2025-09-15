// <vc-preamble>
function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added IsMultiplyPrime helper lemma to verify prime product */
lemma IsMultiplyPrime(x: nat, a: nat, b: nat, c: nat)
    requires Prime(a) && Prime(b) && Prime(c)
    requires x == a * b * c
    ensures exists a': nat, b': nat, c': nat :: Prime(a') && Prime(b') && Prime(c') && x == a' * b' * c'
{
    // Directly satisfy the exists quantifier with the given parameters
}

// </vc-helpers>

// <vc-spec>
method is_multiply_prime(x: nat) returns (ans : bool)

    requires x > 1

    ensures ans <==> exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed prime triple search algorithm */
{
  var found := false;
  var a := 2;
  while a <= x / 4 && !found
    invariant a >= 2
    decreases x - a
  {
    if Prime(a) && x % a == 0 {
      var x1 := x / a;
      var b := 2;
      while b <= x1 / 2 && !found
        invariant b >= 2
        decreases x1 - b
      {
        if Prime(b) && x1 % b == 0 {
          var c := x1 / b;
          if Prime(c) {
            found := true;
            assert Prime(a) && Prime(b) && Prime(c) && x == a * b * c;
            break;
          }
        }
        b := b + 1;
      }
    }
    a := a + 1;
  }
  return found;
}
// </vc-code>
