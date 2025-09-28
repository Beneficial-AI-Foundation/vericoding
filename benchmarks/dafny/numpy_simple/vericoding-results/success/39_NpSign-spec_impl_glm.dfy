// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function sign(x: int): int {
    if x > 0 then 1 else if x == 0 then 0 else -1
}
// </vc-helpers>

// <vc-spec>
method Sign(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length
    ensures
        forall i :: 0 <= i < a.Length ==> (
            (a[i] > 0 ==> result[i] == 1) &&
            (a[i] == 0 ==> result[i] == 0) &&
            (a[i] < 0 ==> result[i] == -1)
        )
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added loop invariant to prove postcondition */
  result := new int[a.Length];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> 
        (a[j] > 0 ==> result[j] == 1) &&
        (a[j] == 0 ==> result[j] == 0) &&
        (a[j] < 0 ==> result[j] == -1)
  {
    result[i] := sign(a[i]);
  }
}
// </vc-code>
