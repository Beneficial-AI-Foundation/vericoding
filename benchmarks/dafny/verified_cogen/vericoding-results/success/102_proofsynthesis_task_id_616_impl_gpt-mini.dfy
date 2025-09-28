// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): safe modulus with nonzero divisor */
function Mod(a: int, b: int): int
  requires b != 0
{ a % b }
// </vc-helpers>

// <vc-spec>
method ElementWiseModule(arr1: array<int>, arr2: array<int>) returns (result: array<int>)
    requires arr1.Length == arr2.Length
    requires forall i :: 0 <= i < arr2.Length ==> arr2[i] != 0
    requires forall i :: 0 <= i < arr1.Length ==> -2147483648 <= arr1[i] % arr2[i] <= 2147483647
    ensures result.Length == arr1.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == arr1[i] % arr2[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): compute elementwise modulus using safe Mod helper */
  var n := arr1.Length;
  result := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> result[k] == Mod(arr1[k], arr2[k])
  {
    result[i] := Mod(arr1[i], arr2[i]);
    i := i + 1;
  }
}
// </vc-code>
