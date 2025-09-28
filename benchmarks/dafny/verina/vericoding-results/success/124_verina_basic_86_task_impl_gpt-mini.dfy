// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): AddMod returns value in [0,n) using named return */
function AddMod(k: int, offset: int, n: int): (r: int)
  requires n > 0
  ensures 0 <= r < n
{
  (k + offset) % n
}
// </vc-helpers>

// <vc-spec>
method rotate(a: array<int>, offset: int) returns (result: array<int>)
    requires offset >= 0
    ensures result.Length == a.Length
    ensures a.Length == 0 ==> result.Length == 0
    ensures a.Length > 0 ==> forall i :: 0 <= i < a.Length ==> 
        result[i] == a[(i + offset) % a.Length]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Implement rotate by copying shifted elements */
  result := new int[a.Length];
  if a.Length > 0 {
    var j := 0;
    while j < a.Length
      invariant 0 <= j <= a.Length
      invariant forall k :: 0 <= k < j ==> result[k] == a[(k + offset) % a.Length]
    {
      var srcIdx := (j + offset) % a.Length;
      result[j] := a[srcIdx];
      j := j + 1;
    }
  }
}
// </vc-code>
