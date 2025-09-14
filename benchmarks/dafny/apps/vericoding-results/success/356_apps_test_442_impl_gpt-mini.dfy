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
lemma even_divides(a: int)
  requires a >= 0 && a % 2 == 0
  ensures 2 * (a / 2) == a
{
  var q := a / 2;
  var m := a % 2;
  // property of div and mod: a == 2*q + m
  assert a == 2 * q + m;
  assert m == 0;
  // hence a == 2*q
}

lemma odd_minus_three_even(r: int)
  requires r % 2 == 1
  ensures (r - 3) % 2 == 0
{
  var q := r / 2;
  var rr := r % 2;
  assert r == 2 * q + rr;
  assert rr == 1;
  assert r - 3 == 2 * q - 2;
  assert r - 3 == 2 * (q - 1);
  // hence r-3 is a multiple of 2
  assert (r - 3) % 2 == 0;
}

lemma ge_from_gt4(r: int)
  requires r > 4
  ensures r - 3 >= 2
{
  // r > 4 implies r >= 5 for integers, so r - 3 >= 2
  assert r - 3 > 1;
  assert r - 3 >= 2;
}

lemma div2_ge1(a: int)
  requires a >= 2
  ensures a / 2 >= 1
{
  // for integers a >= 2, a/2 >= 1
  assert a / 2 >= 1;
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
  if r > 4 && r % 2 == 1 {
    ge_from_gt4(r);
    var k := r - 3;
    odd_minus_three_even(r);
    even_divides(k);
    var y := k / 2;
    result := [1, y];
    div2_ge1(k);
    assert y >= 1;
    // compute H(1,y) = 1*1 + 2*1*y + 1 + 1 = 2*y + 3
    assert H(1, y) == 2 * y + 3;
    // from even_divides we have 2*(k/2) == k, so 2*y == k and thus H(1,y) == r
    assert 2 * y == k;
    assert 2 * y + 3 == r;
    return;
  } else {
    result := [];
    return;
  }
}
// </vc-code>

