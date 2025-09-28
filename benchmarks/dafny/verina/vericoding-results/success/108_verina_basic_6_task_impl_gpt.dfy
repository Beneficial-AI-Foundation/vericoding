// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): basic min function */
function Min(a: int, b: int): int
{
  if a <= b then a else b
}

/* helper modified by LLM (iteration 2): min is one of arguments */
lemma Min_is_one_of(a: int, b: int)
  ensures Min(a, b) == a || Min(a, b) == b
{
  if a <= b {
    assert Min(a, b) == a;
  } else {
    assert Min(a, b) == b;
  }
}

/* helper modified by LLM (iteration 2): min is <= each argument (left) */
lemma Min_le_left(a: int, b: int)
  ensures Min(a, b) <= a
{
  if a <= b {
    assert Min(a, b) == a;
  } else {
    assert b <= a;
    assert Min(a, b) == b;
  }
}

/* helper modified by LLM (iteration 2): min is <= each argument (right) */
lemma Min_le_right(a: int, b: int)
  ensures Min(a, b) <= b
{
  if a <= b {
    assert Min(a, b) == a;
    assert Min(a, b) <= b;
  } else {
    assert Min(a, b) == b;
  }
}
// </vc-helpers>

// <vc-spec>
method MinOfThree(a: int, b: int, c: int) returns (result: int)
    ensures result <= a && result <= b && result <= c
    ensures result == a || result == b || result == c
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): compute min of three using Min and structured proof without lemma calls */
  var x := Min(a, b);
  result := Min(x, c);

  if x <= c {
    assert result == x;
    if a <= b {
      assert x == a;
      assert result <= a;
      assert a <= b;
      assert result <= b;
    } else {
      assert x == b;
      assert b <= a;
      assert result <= a;
      assert result <= b;
    }
    assert result <= c;
  } else {
    assert result == c;
    assert c <= x;
    if a <= b {
      assert x == a;
      assert c <= a;
      assert result <= a;
      assert a <= b;
      assert c <= b;
      assert result <= b;
    } else {
      assert x == b;
      assert b <= a;
      assert c <= b;
      assert result <= b;
      assert c <= a;
      assert result <= a;
    }
    assert result <= c;
  }

  // show equality to one of a, b, or c
  if result == x {
    if a <= b {
      assert x == a;
      assert result == a;
    } else {
      assert x == b;
      assert result == b;
    }
  } else {
    assert result == c;
  }
}
// </vc-code>
