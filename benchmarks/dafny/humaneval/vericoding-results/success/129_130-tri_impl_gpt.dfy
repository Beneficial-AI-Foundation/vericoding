// <vc-preamble>
function tri(n: nat): nat
  decreases if n % 2 == 0 then 0 else n
{
  if n == 1 then 3
  else if n % 2 == 0 then 1 + n / 2
  else tri(n - 1) + tri(n - 2) + tri(n + 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple identity function for natural numbers */
function IdNat(x: nat): nat { x }
// </vc-helpers>

// <vc-spec>
method Tribonacci(n: nat) returns (result: seq<nat>)

  ensures |result| == n + 1
  ensures forall i :: 0 <= i <= n ==> result[i] == tri(i)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): build the result sequence iteratively to satisfy the specification */
  var i: nat := 0;
  result := [];
  while i <= n
    invariant 0 <= i <= n + 1
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == tri(j)
    decreases n - i
  {
    result := result + [tri(i)];
    i := i + 1;
  }
}
// </vc-code>
