// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsDivisibleBy3(n: int) { n % 3 == 0 }
// </vc-helpers>

// <vc-spec>
method Myfun4(x: array<int>, y: array<int>) returns ()
    requires y.Length == 0
    ensures forall k :: 0 <= k < y.Length ==> y[k] % 3 == 0 && y[k] in x[..]
// </vc-spec>
// <vc-code>
{
  assert y.Length == 0;
}
// </vc-code>
