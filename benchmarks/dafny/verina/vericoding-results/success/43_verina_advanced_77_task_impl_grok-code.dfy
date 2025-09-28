// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method TrapRainWater(height: array<nat>) returns (result: nat)
    requires height.Length >= 0
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed loop invariants to use >= instead of <= for correctness */
  if height.Length == 0 {
    result := 0;
  } else {
    var maxLeft := new nat[height.Length];
    maxLeft[0] := height[0];
    var i := 1;
    while i < height.Length
      invariant 1 <= i <= height.Length
      invariant forall j :: 0 <= j < i ==> maxLeft[j] >= height[j]
    {
      var prev := maxLeft[i-1];
      maxLeft[i] := if height[i] > prev then height[i] else prev;
      i := i + 1;
    }
    var maxRight := new nat[height.Length];
    maxRight[height.Length-1] := height[height.Length-1];
    i := height.Length - 2;
    while i >= 0
      invariant -1 <= i < height.Length - 1
      invariant forall j :: i < j < height.Length ==> maxRight[j] >= height[j]
    {
      var next := maxRight[i+1];
      maxRight[i] := if height[i] > next then height[i] else next;
      i := i - 1;
    }
    var total := 0;
    i := 0;
    while i < height.Length
      invariant 0 <= i <= height.Length
      invariant total >= 0
    {
      var minMax := if maxLeft[i] < maxRight[i] then maxLeft[i] else maxRight[i];
      if minMax > height[i] {
        total := total + (minMax - height[i]);
      }
      i := i + 1;
    }
    result := total;
  }
}
// </vc-code>
