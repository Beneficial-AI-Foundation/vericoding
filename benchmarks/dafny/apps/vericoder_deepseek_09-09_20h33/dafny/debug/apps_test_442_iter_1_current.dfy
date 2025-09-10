function H(x: int, y: int): int
{
    x * x + 2 * x * y + x + 1
}

predicate ValidInput(r: int)
{
    r > 0
}

predicate ValidSolution(result: seq<int>, r: int)
{
    if |result| == 0 then
        true
    else
        |result| == 2 && result[0] > 0 && result[1] > 0 && H(result[0], result[1]) == r
}

predicate HasSolution(r: int)
{
    r > 4 && r % 2 == 1
}

// <vc-helpers>
lemma HProperty1(a: int, b: int)
  requires a > 0 && b > 0
  ensures H(a, b) == a * (a + 2 * b + 1) + 1
{
}

lemma HProperty2(r: int, x: int, y: int)
  requires r > 4 && r % 2 == 1
  requires x == 1 && y == (r - 3) / 2
  ensures y > 0
{
  calc {
    y;
    (r - 3) / 2;
    > 0;    // Since r > 4, r-3 > 1, so (r-3)/2 > 0
  }
}

lemma HProperty3(r: int, x: int, y: int)
  requires r > 4 && r % 2 == 1
  requires x == 1 && y == (r - 3) / 2
  ensures H(x, y) == r
{
  calc {
    H(1, y);
    1 * 1 + 2 * 1 * y + 1 + 1;
    { HProperty1(1, y); }
    2 + 2 * y;
    { assert y == (r - 3) / 2; }
    2 + 2 * ((r - 3) / 2);
    { assert r - 3 >= 2 && (r - 3) % 2 == 0; }  // r is odd, so r-3 is even
    r;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(r: int) returns (result: seq<int>)
    requires ValidInput(r)
    ensures ValidSolution(result, r)
    ensures |result| == 0 || |result| == 2
    ensures |result| == 2 ==> result[0] > 0 && result[1] > 0
    ensures |result| == 2 ==> H(result[0], result[1]) == r
    ensures r <= 4 ==> |result| == 0
    ensures r > 4 && r % 2 == 0 ==> |result| == 0
    ensures r > 4 && r % 2 == 1 ==> |result| == 2 && result[0] == 1 && result[1] == (r - 3) / 2
// </vc-spec>
// <vc-code>
{
  if r <= 4 || r % 2 == 0 {
    result := [];
  } else {
    var x := 1;
    var y := (r - 3) / 2;
    HProperty2(r, x, y);
    result := [x, y];
  }
}
// </vc-code>

