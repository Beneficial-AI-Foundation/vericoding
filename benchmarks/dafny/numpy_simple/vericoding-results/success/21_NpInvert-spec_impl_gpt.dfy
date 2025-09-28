// <vc-preamble>
function pow2(n: nat): nat 
    decreases n
{
    if n == 0 then
        1
    else
        2 * pow2(n - 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): change mask to return int to avoid nat subtraction issues */
function mask(bit_width: nat): int {
  pow2(bit_width) - 1
}

// </vc-helpers>

// <vc-spec>
method invert(bit_width: nat, a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        forall i :: 0 <= i < a.Length ==> result[i] == (pow2(bit_width) - 1) - a[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): construct result by subtracting each element from the computed mask */
  var n := a.Length;
  var m := pow2(bit_width) - 1;
  var r := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant r.Length == n
    invariant forall j :: 0 <= j < i ==> r[j] == m - a[j]
    decreases n - i
  {
    r[i] := m - a[i];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
