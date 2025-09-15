// <vc-preamble>
function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}
// </vc-preamble>

// <vc-helpers>
function IsPrimeFactor(n: nat, p: nat): bool
  requires n > 1
  requires p > 0
{
  Prime(p) && n % p == 0
}

function FindFirstPrimeFactor(n: nat): nat
  requires n > 1
  ensures IsPrimeFactor(n, FindFirstPrimeFactor(n))
{
  if n == 2 then 
    2
  else
    var k := 2;
    while k <= n
      decreases n - k
      invariant k >= 2
      invariant forall i: nat | 1 < i < k :: !IsPrimeFactor(n, i)
    {
      if IsPrimeFactor(n, k) {
        return k;
      }
      k := k + 1;
    }
    n
}

lemma ThreePrimesLemma(x: nat)
  requires x > 1
  ensures exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c
  decreases x
{
  if exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c {
  }
  else {
    forall a: nat, b: nat, c: nat | Prime(a) && Prime(b) && Prime(c) {
      assert a * b * c != x;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method is_multiply_prime(x: nat) returns (ans : bool)

    requires x > 1

    ensures ans <==> exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed syntax error and simplified logic */
  ans := false;
  
  var a := 2;
  while a <= x
    decreases x - a
    invariant a >= 2
  {
    if Prime(a) && x % a == 0 {
      var rem := x / a;
      var b := 2;
      while b <= rem
        decreases rem - b
        invariant b >= 2
      {
        if Prime(b) && rem % b == 0 {
          var c := rem / b;
          if Prime(c) && a * b * c == x {
            ans := true;
            return;
          }
        }
        b := b + 1;
      }
    }
    a := a + 1;
  }
}
// </vc-code>
