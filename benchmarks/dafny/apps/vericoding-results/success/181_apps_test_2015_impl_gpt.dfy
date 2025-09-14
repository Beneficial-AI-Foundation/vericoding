predicate ValidInput(r: int, g: int, b: int)
{
    r >= 1 && g >= 1 && b >= 1
}

function MaxOf3(r: int, g: int, b: int): int
{
    if r >= g && r >= b then r
    else if g >= r && g >= b then g
    else b
}

predicate CanArrange(r: int, g: int, b: int)
    requires ValidInput(r, g, b)
{
    var maxCount := MaxOf3(r, g, b);
    var total := r + g + b;
    2 * maxCount <= total + 1
}

// <vc-helpers>
lemma MaxOf3_is_if(r: int, g: int, b: int)
    ensures MaxOf3(r, g, b) == (if r >= g && r >= b then r else if g >= r && g >= b then g else b)
{
    if r >= g && r >= b {
        assert MaxOf3(r, g, b) == r;
    } else if g >= r && g >= b {
        assert MaxOf3(r, g, b) == g;
    } else {
        assert MaxOf3(r, g, b) == b;
    }
}

lemma CanArrange_unfold(r: int, g: int, b: int)
    requires ValidInput(r, g, b)
    ensures CanArrange(r, g, b) == (2 * MaxOf3(r, g, b) <= r + g + b + 1)
{
    if CanArrange(r, g, b) {
        assert 2 * MaxOf3(r, g, b) <= r + g + b + 1;
    } else {
        assert !(2 * MaxOf3(r, g, b) <= r + g + b + 1);
    }
}
// </vc-helpers>

// <vc-spec>
method CheckLampArrangement(r: int, g: int, b: int) returns (result: bool)
    requires ValidInput(r, g, b)
    ensures result == CanArrange(r, g, b)
// </vc-spec>
// <vc-code>
{
  var total := r + g + b;
  var m := if r >= g && r >= b then r else if g >= r && g >= b then g else b;
  result := 2 * m <= total + 1;

  assert result == (2 * m <= total + 1);

  assert m == (if r >= g && r >= b then r else if g >= r && g >= b then g else b);
  assert MaxOf3(r, g, b) == (if r >= g && r >= b then r else if g >= r && g >= b then g else b);
  assert m == MaxOf3(r, g, b);

  assert total == r + g + b;

  assert (2 * m <= total + 1) == (2 * MaxOf3(r, g, b) <= r + g + b + 1);
  assert CanArrange(r, g, b) == (2 * MaxOf3(r, g, b) <= r + g + b + 1);

  assert result == CanArrange(r, g, b);
}
// </vc-code>

