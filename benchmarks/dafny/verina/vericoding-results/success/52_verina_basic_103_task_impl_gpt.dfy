// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function isSpecialIndex(i: int): bool {
  i == 4 || i == 7
}

/* helper modified by LLM (iteration 3): removed redundant non-null requires to avoid warning; kept reads frame */
function desiredValue(a: array<int>, i: int): int
  requires a.Length >= 8
  requires 0 <= i < a.Length
  reads a
{
  if i == 4 then a[4] + 3 else if i == 7 then 516 else a[i]
}
// </vc-helpers>

// <vc-spec>
method update_elements(a: array<int>) returns (result: array<int>)
    requires a.Length >= 8
    ensures result.Length == a.Length
    ensures result[4] == a[4] + 3
    ensures result[7] == 516
    ensures forall i :: 0 <= i < a.Length && i != 4 && i != 7 ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): element-wise copy with special updates; removed redundant null invariant */
  var n := a.Length;
  result := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant forall j :: 0 <= j < i && j != 4 && j != 7 ==> result[j] == a[j]
    invariant 4 < i ==> result[4] == a[4] + 3
    invariant 7 < i ==> result[7] == 516
    decreases n - i
  {
    if i == 4 {
      result[i] := a[i] + 3;
    } else if i == 7 {
      result[i] := 516;
    } else {
      result[i] := a[i];
    }
    i := i + 1;
  }
}
// </vc-code>
