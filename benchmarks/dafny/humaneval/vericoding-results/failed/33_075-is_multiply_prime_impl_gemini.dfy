// <vc-preamble>
function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}
// </vc-preamble>

// <vc-helpers>
lemma LemmaMulDiv(a: nat, b: nat)
    requires b > 0
    requires a % b == 0
    ensures (a / b) * b == a
{}
// </vc-helpers>

// <vc-spec>
method is_multiply_prime(x: nat) returns (ans : bool)

    requires x > 1

    ensures ans <==> exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c
// </vc-spec>
// <vc-code>
{
  ans := false;
  var a := 2;
  while a < x && !ans {
    if Prime(a) && x % a == 0 {
      var rem1 := x / a;
      if rem1 > 1 {
        var b := 2;
        while b < rem1 && !ans {
          if Prime(b) && rem1 % b == 0 {
            var c := rem1 / b;
            if Prime(c) {
              // Prove that we found a valid decomposition
              LemmaMulDiv(x, a);
              LemmaMulDiv(rem1, b);
              // By the lemmas: x == a * rem1 and rem1 == b * c
              // Therefore, x == a * b * c, satisfying the existential
              ans := true;
            }
          }
          b := b + 1;
        }
      }
    }
    a := a + 1;
  }
}
// </vc-code>
