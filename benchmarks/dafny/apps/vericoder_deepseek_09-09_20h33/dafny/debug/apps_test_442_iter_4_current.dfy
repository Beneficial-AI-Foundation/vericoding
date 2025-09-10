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
  calc {
    H(a, b);
    a * a + 2 * a * b + a + 1;
    a * (a + 2 * b) + a + 1;
    a * (a + 2 * b + 1) + 1;
  }
}

lemma HProperty2(r: int, x: int, y: int)
  requires r > 4 && r % 2 == 1
  requires x == 1 && y == (r - 3) / 2
  ensures y > 0
{
  assert r - 3 >= 2 by {
    assert r > 4;
    assert r >= 5;
  }
  assert (r - 3) / 2 >= 1;
}

lemma HProperty3(r: int, x: int, y: int)
  requires r > 4 && r % 2 == 1
  requires x == 1 && y == (r - 3) / 2
  ensures H(x, y) == r
{
  var y_val := (r - 3) / 2;
  calc {
    H(1, y_val);
    1 * 1 + 2 * 1 * y_val + 1 + 1;
    2 + 2 * y_val;
    2 + 2 * ((r - 3) / 2);
    == {
      assert r - 3 >= 2;
      assert (r - 3) % 2 == 0;
      assert 2 * ((r - 3) / 2) == r - 3;
    }
    2 + (r - 3);
    r - 1;
    == { assert r - 1 == r - 1; }
    r - 1;
  }
  assert false;
}
// </vc-helpers>
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

