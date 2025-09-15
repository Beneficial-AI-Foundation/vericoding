// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Changed precondition to x < y to ensure there's at least one even number and avoid x==y odd case */
predicate IsEven(n: int) {
  n % 2 == 0
}

/* helper modified by LLM (iteration 3): Changed precondition to x < y to ensure there's at least one even number and avoid x==y odd case */
function LargestEven(x: int, y: int): int
  requires 0 <= x && 0 <= y
  requires x < y
  ensures IsEven(LargestEven(x, y))
  ensures x <= LargestEven(x, y) && LargestEven(x, y) <= y
  ensures forall i: int :: x <= i <= y && IsEven(i) ==> LargestEven(x, y) >= i
{
  if IsEven(y) then y else y - 1
}
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
  /* code modified by LLM (iteration 3): No changes needed */
  if x >= y {
    num := -1;
  } else {
    num := LargestEven(x, y);
  }
}
// </vc-code>
