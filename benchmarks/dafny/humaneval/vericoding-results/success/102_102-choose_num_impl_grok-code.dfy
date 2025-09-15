// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method choose_num(x : int, y : int) returns (num : int)

  requires 0 <= x && 0 <= y

  ensures num == -1 || (num >= x && num <= y)
  ensures num == -1 || num % 2 == 0
  ensures num == -1 || (forall i : int :: x <= i <= y && i % 2 == 0 ==> num >= i)
  ensures num == -1 <==> x >= y
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): adjusted logic to return -1 when x >= y */
  if x >= y {
    return -1;
  }
  var cand := y - (y % 2);
  if cand >= x {
    return cand;
  } else {
    return -1;
  }
}
// </vc-code>
