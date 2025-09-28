// <vc-preamble>

function AbsDiff(x: real, y: real): real
{
  if x >= y then x - y else y - x
}

predicate ValidInput(numbers: seq<real>)
{
  |numbers| >= 2
}

predicate IsOptimalPair(numbers: seq<real>, pair: (real, real))
{
  pair.0 in numbers &&
  pair.1 in numbers &&
  pair.0 <= pair.1 &&
  forall i, j :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j ==>
    AbsDiff(numbers[i], numbers[j]) >= AbsDiff(pair.0, pair.1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): explicit proof of symmetry of AbsDiff */
lemma AbsDiffSym(x: real, y: real)
  ensures AbsDiff(x, y) == AbsDiff(y, x)
{
  if x >= y {
    assert AbsDiff(x, y) == x - y;
    assert AbsDiff(y, x) == x - y;
  } else {
    assert AbsDiff(x, y) == y - x;
    assert AbsDiff(y, x) == y - x;
  }
}

/* helper modified by LLM (iteration 3): lift bound over ordered pairs to all distinct pairs using symmetry */
lemma OrderedToUnordered(numbers: seq<real>, bestDiff: real)
  requires forall p:int, q:int :: 0 <= p < q < |numbers| ==> bestDiff <= AbsDiff(numbers[p], numbers[q])
  ensures forall i:int, j:int :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j ==> bestDiff <= AbsDiff(numbers[i], numbers[j])
{
  forall i:int, j:int
    ensures 0 <= i < |numbers| && 0 <= j < |numbers| && i != j ==> bestDiff <= AbsDiff(numbers[i], numbers[j])
  {
    if 0 <= i < |numbers| && 0 <= j < |numbers| && i != j {
      if i < j {
        assert 0 <= i && i < j && j < |numbers|;
        assert bestDiff <= AbsDiff(numbers[i], numbers[j]);
      } else {
        assert 0 <= j && j < i && i < |numbers|;
        assert bestDiff <= AbsDiff(numbers[j], numbers[i]);
        calc {
          bestDiff;
          <= { }
          AbsDiff(numbers[j], numbers[i]);
          == { AbsDiffSym(numbers[j], numbers[i]); }
          AbsDiff(numbers[i], numbers[j]);
        }
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method find_closest_elements(numbers: seq<real>) returns (result: (real, real))
  requires ValidInput(numbers)
  ensures IsOptimalPair(numbers, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): O(n^2) search for closest pair with invariants; conclude global optimality via helper lemma */
  var n := |numbers|;
  var a0 := numbers[0];
  var a1 := numbers[1];
  if a0 <= a1 {
    result := (a0, a1);
  } else {
    result := (a1, a0);
  }
  var bestDiff: real := AbsDiff(result.0, result.1);
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |numbers| == n
    invariant result.0 in numbers && result.1 in numbers
    invariant result.0 <= result.1
    invariant bestDiff == AbsDiff(result.0, result.1)
    invariant forall p:int, q:int :: 0 <= p < q < n && (p < i) ==> bestDiff <= AbsDiff(numbers[p], numbers[q])
  {
    var j := i + 1;
    while j < n
      invariant i < n ==> j >= i + 1 && j <= n
      invariant |numbers| == n
      invariant result.0 in numbers && result.1 in numbers
      invariant result.0 <= result.1
      invariant bestDiff == AbsDiff(result.0, result.1)
      invariant forall p:int, q:int :: 0 <= p < q < n && ((p < i) || (p == i && q < j)) ==> bestDiff <= AbsDiff(numbers[p], numbers[q])
    {
      var d := AbsDiff(numbers[i], numbers[j]);
      if d < bestDiff {
        var x := numbers[i];
        var y := numbers[j];
        if x <= y {
          result := (x, y);
        } else {
          result := (y, x);
        }
        bestDiff := AbsDiff(result.0, result.1);
      }
      j := j + 1;
    }
    i := i + 1;
  }
  assert i == n;
  assert bestDiff == AbsDiff(result.0, result.1);
  assert forall p:int, q:int :: 0 <= p < q < n ==> bestDiff <= AbsDiff(numbers[p], numbers[q]);
  OrderedToUnordered(numbers, bestDiff);
}
// </vc-code>
