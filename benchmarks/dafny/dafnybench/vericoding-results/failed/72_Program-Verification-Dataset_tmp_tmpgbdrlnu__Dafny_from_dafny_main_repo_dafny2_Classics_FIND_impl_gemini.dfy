// <vc-preamble>
ghost function Factorial(n: nat): nat
{
  if n == 0 then 1 else n * Factorial(n-1)
}
// </vc-preamble>

// <vc-helpers>
ghost function seq_le_seq<T>(s1: seq<T>, s2: seq<T>): bool
{
  forall i, j :: 0 <= i < |s1| && 0 <= j < |s2| ==> s1[i] <= s2[j]
}
// </vc-helpers>

// <vc-spec>
method FIND(A: array<int>, N: int, f: int)
  requires A.Length == N;
  requires 0 <= f < N;
  modifies A;
  ensures forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[q];
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var j := N - 1;

  while i <= f && f <= j
    invariant 0 <= i <= f + 1
    invariant f <= j < N
    invariant multiset(A[..]) == multiset(old(A[..]))
  {
    if i == j {
        break;
    }
    if A[i] > A[j] {
        A[i], A[j] := A[j], A[i];
    }

    if i < f {
        i := i + 1;
    } else if j > f {
        j := j - 1;
    } else {
        // This case occurs when i == f and j == f, handled by loop condition.
        break;
    }
  }
}
// </vc-code>
