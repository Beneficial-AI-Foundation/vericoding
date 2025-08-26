// I'll need a helper lemma to prove that repeated addition is equivalent to multiplication.

// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false


// A version of Turing's additive factorial program [Dr. A. Turing, "Checking a large routine",
// In "Report of a Conference of High Speed Automatic Calculating Machines", pp. 67-69, 1949].

ghost function Factorial(n: nat): nat
{
  if n == 0 then 1 else n * Factorial(n-1)
}

// <vc-helpers>
function RepeatAdd(a: nat, times: nat, acc: nat): nat
{
  if times == 0 then acc else RepeatAdd(a, times - 1, acc + a)
}

lemma RepeatAddEquivalent(a: nat, times: nat, acc: nat)
  ensures RepeatAdd(a, times, acc) == acc + a * times
{
  if times == 0 {
    assert RepeatAdd(a, 0, acc) == acc;
    assert acc + a * 0 == acc + 0 == acc;
  } else {
    RepeatAddEquivalent(a, times - 1, acc + a);
    assert RepeatAdd(a, times - 1, acc + a) == (acc + a) + a * (times - 1);
    assert (acc + a) + a * (times - 1) == acc + a + a * (times - 1);
    assert a + a * (times - 1) == a * times;
    assert acc + a + a * (times - 1) == acc + a * times;
  }
}

lemma MultiplicationByRepeatedAddition(a: nat, b: nat)
  ensures a * b == RepeatAdd(a, b, 0)
{
  RepeatAddEquivalent(a, b, 0);
  assert RepeatAdd(a, b, 0) == 0 + a * b == a * b;
}

lemma RepeatAddRecursive(a: nat, b: nat)
  requires b > 0
  ensures RepeatAdd(a, b, 0) == a + RepeatAdd(a, b - 1, 0)
{
  RepeatAddEquivalent(a, b, 0);
  RepeatAddEquivalent(a, b - 1, 0);
  assert RepeatAdd(a, b, 0) == a * b;
  assert RepeatAdd(a, b - 1, 0) == a * (b - 1);
  assert a * b == a + a * (b - 1);
}
// </vc-helpers>

// <vc-spec>
method AdditiveFactorial(n: nat) returns (u: nat)
  ensures u == Factorial(n)
// </vc-spec>
// <vc-code>
{
  u := 1;
  var i := 1;
  
  while i <= n
    invariant 1 <= i <= n + 1
    invariant u == Factorial(i - 1)
  {
    var temp := 0;
    var j := 0;
    
    while j < i
      invariant 0 <= j <= i
      invariant temp == u * j
    {
      temp := temp + u;
      j := j + 1;
      assert temp == u * j; // u * (old(j) + 1) == u * old(j) + u == old(temp) + u
    }
    
    assert temp == u * i;
    assert u == Factorial(i - 1);
    assert temp == Factorial(i - 1) * i == i * Factorial(i - 1) == Factorial(i);
    u := temp;
    i := i + 1;
  }
}
// </vc-code>

// Hoare's FIND program [C.A.R. Hoare, "Proof of a program: FIND", CACM 14(1): 39-45, 1971].
// The proof annotations here are not the same as in Hoare's article.

// In Hoare's words:
//   This program operates on an array A[1:N], and a value of f (1 <= f <= N).
//   Its effect is to rearrange the elements of A in such a way that:
//     forall p,q (1 <= p <= f <= q <= N ==> A[p] <= A[f] <= A[q]).
//
// Here, we use 0-based indices, so we would say:
//   This method operates on an array A[0..N], and a value of f (0 <= f < N).
//   Its effect is to rearrange the elements of A in such a way that:
//     forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[f] <= A[q]).