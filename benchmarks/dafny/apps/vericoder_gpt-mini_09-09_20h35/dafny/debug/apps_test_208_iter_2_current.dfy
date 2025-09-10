predicate ValidInput(x1: int, y1: int, x2: int, y2: int)
{
    -100 <= x1 <= 100 && -100 <= y1 <= 100 && -100 <= x2 <= 100 && -100 <= y2 <= 100
}

predicate IsInvalidCase(x1: int, y1: int, x2: int, y2: int)
{
    x1 != x2 && y1 != y2 && abs(x1 - x2) != abs(y1 - y2)
}

predicate IsDiagonalCase(x1: int, y1: int, x2: int, y2: int)
{
    x1 != x2 && y1 != y2 && abs(x1 - x2) == abs(y1 - y2)
}

predicate IsVerticalEdgeCase(x1: int, y1: int, x2: int, y2: int)
{
    x1 == x2
}

predicate IsHorizontalEdgeCase(x1: int, y1: int, x2: int, y2: int)
{
    x1 != x2 && y1 == y2
}

function ExpectedDiagonalResult(x1: int, y1: int, x2: int, y2: int): seq<int>
{
    [x1, y2, x2, y1]
}

function ExpectedVerticalResult(x1: int, y1: int, x2: int, y2: int): seq<int>
{
    [x1 + abs(y2 - y1), y1, x1 + abs(y2 - y1), y2]
}

function ExpectedHorizontalResult(x1: int, y1: int, x2: int, y2: int): seq<int>
{
    [x1, y1 + abs(x2 - x1), x2, y1 + abs(x2 - x1)]
}

predicate ValidOutput(result: seq<int>)
{
    (|result| == 1 && result[0] == -1) ||
    (|result| == 4 && (forall i :: 0 <= i < 4 ==> -1000 <= result[i] <= 1000))
}

// <vc-helpers>
function abs(x: int): int
{
  if x >= 0 then x else -x
}

lemma DiffBound(a: int, b: int)
  requires -100 <= a <= 100 && -100 <= b <= 100
  ensures abs(a - b) <= 200
{
  // a - b <= 200
  calc {
    a - b;
    <= {
      assert a <= 100;
    }
    100 - b;
    <= {
      assert -100 <= b;
    }
    200;
  }
  // b - a <= 200
  calc {
    b - a;
    <= {
      assert b <= 100;
    }
    100 - a;
    <= {
      assert -100 <= a;
    }
    200;
  }
  if a - b >= 0 {
    assert abs(a - b) == a - b;
    assert a - b <= 200;
  } else {
    assert abs(a - b) == b - a;
    assert b - a <= 200;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(x1: int, y1: int, x2: int, y2: int) returns (result: seq<int>)
    requires ValidInput(x1, y1, x2, y2)
    ensures ValidOutput(result)
    ensures IsInvalidCase(x1, y1, x2, y2) ==> result == [-1]
    ensures IsDiagonalCase(x1, y1, x2, y2) ==> result == ExpectedDiagonalResult(x1, y1, x2, y2)
    ensures IsVerticalEdgeCase(x1, y1, x2, y2) ==> result == ExpectedVerticalResult(x1, y1, x2, y2)
    ensures IsHorizontalEdgeCase(x1, y1, x2, y2) ==> result == ExpectedHorizontalResult(x1, y1, x2, y2)
// </vc-spec>
// <vc-code>
{
  if IsInvalidCase(x1, y1, x2, y2) {
    result := [-1];
    assert |result| == 1 && result[0] == -1;
    return;
  }

  if IsDiagonalCase(x1, y1, x2, y2) {
    result := [x1, y2, x2, y1];
    // elements are within [-100,100] due to ValidInput, hence within [-1000,1000]
    assert -100 <= x1 && x1 <= 100;
    assert -100 <= y2 && y2 <= 100;
    assert -100 <= x2 && x2 <= 100;
    assert -100 <= y1 && y1 <= 100;
    assert forall i :: 0 <= i < 4 ==> -1000 <= result[i] <= 1000;
    assert ValidOutput(result);
    return;
  }

  if IsVerticalEdgeCase(x1, y1, x2, y2) {
    // prove abs(y2 - y1) <= 200
    DiffBound(y2, y1);
    var t := x1 + abs(y2 - y1);
    result := [t, y1, t, y2];
    // bounds: x1 in [-100,100], abs(y2-y1) <= 200 => t in [-100,300] subset of [-1000,1000]
    assert -100 <= x1 && x1 <= 100;
    assert abs(y2 - y1) <= 200;
    assert t >= x1;
    assert t <= 100 + 200;
    assert forall i :: 0 <= i < 4 ==> -1000 <= result[i] <= 1000;
    assert ValidOutput(result);
    return;
  }

  // Horizontal case (y1 == y2 and x1 != x2)
  DiffBound(x2, x1);
  var s := y1 + abs(x2 - x1);
  result := [x1, s, x2, s];
  // bounds: y1 in [-100,100], abs(x2-x1) <= 200 => s in [-100,300] subset of [-1000,1000]
  assert -100 <= y1 && y1 <= 100;
  assert abs(x2 - x1) <= 200;
  assert s >= y1;
  assert s <= 100 + 200;
  assert forall i :: 0 <= i < 4 ==> -1000 <= result[i] <= 1000;
  assert ValidOutput(result);
  return;
}
// </vc-code>

