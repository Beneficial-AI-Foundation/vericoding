// <vc-preamble>
function factorial_spec(n : int) : int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else n * factorial_spec(n - 1)
}
function sum_spec(n : int) : int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else n + sum_spec(n - 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): define value at index based on parity */
function valueAt(i: int) : int
  requires i >= 0
{
  if i % 2 == 0 then factorial_spec(i) else sum_spec(i)
}
// </vc-helpers>

// <vc-spec>
method f(n : int) returns (result : seq<int>)

  requires n >= 1

  ensures |result| == n
  ensures forall i : int :: i >= 0 && i < |result| && i % 2 == 0 ==> result[i] == factorial_spec(i)
  ensures forall i : int :: i >= 0 && i < |result| && i % 2 != 0 ==> result[i] == sum_spec(i)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): build sequence iteratively with parity-specific values and invariants */
  var r: seq<int> := [];
  var i: int := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |r| == i
    invariant forall j: int :: 0 <= j < |r| && j % 2 == 0 ==> r[j] == factorial_spec(j)
    invariant forall j: int :: 0 <= j < |r| && j % 2 != 0 ==> r[j] == sum_spec(j)
  {
    var v := if i % 2 == 0 then factorial_spec(i) else sum_spec(i);
    r := r + [v];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
