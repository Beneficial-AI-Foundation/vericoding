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
  if x >= y {
    num := -1;
  } else {
    if y % 2 == 0 {
      num := y;
    } else {
      // y is odd. x < y implies x <= y - 1.
      // So y - 1 is an even number in the range [x, y].
      // It is the largest such number because any other even number j must be j <= y,
      // and since y is odd, j must be j <= y - 1.
      num := y - 1;
    }
  }
}
// </vc-code>
