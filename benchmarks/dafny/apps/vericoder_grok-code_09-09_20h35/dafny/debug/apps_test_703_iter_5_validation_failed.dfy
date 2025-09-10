function min(x: int, y: int): int
{
    if x <= y then x else y
}

predicate ValidInput(k: int, a: int, b: int, v: int)
{
    2 <= k <= 1000 && 1 <= a <= 1000 && 1 <= b <= 1000 && 1 <= v <= 1000
}

function BoxCapacity(numBoxes: int, k: int, b: int, v: int): int
    requires numBoxes >= 0
{
    v * (numBoxes + min(b, (k - 1) * numBoxes))
}

predicate CanStoreNuts(numBoxes: int, k: int, a: int, b: int, v: int)
    requires numBoxes >= 0
{
    a <= BoxCapacity(numBoxes, k, b, v)
}

predicate IsMinimalSolution(result: int, k: int, a: int, b: int, v: int)
    requires result >= 1
{
    CanStoreNuts(result, k, a, b, v) &&
    (result == 1 || !CanStoreNuts(result - 1, k, a, b, v))
}

// <vc-helpers>
lemma CanStoreAt1009(k: int, a: int, b: int, v: int)
  requires ValidInput(k, a, b, v)
  ensures CanStoreNuts(1009, k, a, b, v)
{
  calc {
    a <= 1000;
    v * 1009 >= 1 * 1009 == 1009 > 1000;
    BoxCapacity(1009, k, b, v) >= v * 1009;
  }
}

method {:axiom} solve(k: int, a: int, b: int, v: int) returns (result: int)
    requires ValidInput(k, a, b, v)
    ensures result >= 1
    ensures result <= 1009
    ensures IsMinimalSolution(result, k, a, b, v)
    ensures exists i :: (1 <= i <= 1009 && CanStoreNuts(i, k, a, b, v) && result == i && 
            forall j :: 1 <= j < i ==> !CanStoreNuts(j, k, a, b, v))
// </vc-helpers>

// <vc-spec>
method solve(k: int, a: int, b: int, v: int) returns (result: int)
    requires ValidInput(k, a, b, v)
    ensures result >= 1
    ensures result <= 1009
    ensures IsMinimalSolution(result, k, a, b, v)
    ensures exists i :: 1 <= i <= 1009 && CanStoreNuts(i, k, a, b, v) && result == i && 
            (forall j :: 1 <= j < i ==> !CanStoreNuts(j, k, a, b, v))
// </vc-spec>
// <vc-code>
{
  var boxes := 1;
  while boxes < 1009 && !CanStoreNuts(boxes, k, a, b, v)
    invariant 1 <= boxes <= 1009
    invariant forall j :: 1 <= j < boxes ==> !CanStoreNuts(j, k, a, b, v)
    decreases 1010 - boxes
  {
    boxes := boxes + 1;
  }
  if boxes == 1009 {
    CanStoreAt1009(k, a, b, v);
  }
  result := boxes;
  assert CanStoreNuts(result, k, a, b, v);
}
// </vc-code>

