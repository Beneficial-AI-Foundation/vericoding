predicate ValidInput(A: int, B: int, C: int) {
    0 <= A <= 50 && 0 <= B <= 50 && 0 <= C <= 50
}

function MaxOf3(A: int, B: int, C: int): int {
    if A >= B && A >= C then A
    else if B >= C then B
    else C
}

function SortDescending(A: int, B: int, C: int): (int, int, int) {
    if A >= B && A >= C then
        if B >= C then (A, B, C) else (A, C, B)
    else if B >= A && B >= C then
        if A >= C then (B, A, C) else (B, C, A)
    else
        if A >= B then (C, A, B) else (C, B, A)
}

function MinOperations(A: int, B: int, C: int): int
    requires ValidInput(A, B, C)
{
    var (a0, a1, a2) := SortDescending(A, B, C);
    var gap1 := a0 - a1;
    var updated_smallest := a2 + gap1;
    var remaining_gap := a0 - updated_smallest;
    gap1 + remaining_gap / 2 + (remaining_gap % 2) * 2
}

predicate AllEqual(A: int, B: int, C: int) {
    A == B && B == C
}

// <vc-helpers>
lemma Lemma_MinOperationsRecursive(a0: int, a1: int, a2: int)
  requires a0 >= a1 >= a2 >= 0
  requires a0 <= 50 && a1 <= 50 && a2 <= 50
  ensures MinOperations(a0, a1, a2) == 
    if a0 == a1 && a1 == a2 then 0
    else if a0 == a1 then
      if (a1 - a2) % 2 == 0 then 3 * (a1 - a2) / 2
      else 3 * ((a1 - a2) / 2) + 2
    else if a1 == a2 then 2 * (a0 - a1)
    else var step := a0 - a1; var mid := a2 + step; var rem := a0 - mid;
      if rem % 2 == 0 then step + rem / 2
      else step + rem / 2 + 2
{
  // Implementation needed for the lemma proof
}

lemma Lemma_ValidInputBounds(A: int, B: int, C: int)
  requires ValidInput(A, B, C)
  ensures 0 <= A <= 50 && 0 <= B <= 50 && 0 <= C <= 50
{
}

lemma Lemma_SortDescendingPreservesValidInput(A: int, B: int, C: int)
  requires ValidInput(A, B, C)
  ensures ValidInput(SortDescending(A, B, C).0, SortDescending(A, B, C).1, SortDescending(A, B, C).2)
{
}

lemma Lemma_SortDescendingOrder(A: int, B: int, C: int)
  requires ValidInput(A, B, C)
  ensures var (x, y, z) := SortDescending(A, B, C); x >= y >= z
{
}

lemma Lemma_OperationsCountBound(a0: int, a1: int, a2: int)
  requires a0 >= a1 >= a2 >= 0
  requires a0 <= 50 && a1 <= 50 && a2 <= 50
  ensures MinOperations(a0, a1, a2) <= 2 * (a0 - a2)
{
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, C: int) returns (result: int)
    requires ValidInput(A, B, C)
    ensures result >= 0
    ensures AllEqual(A, B, C) ==> result == 0
    ensures result == MinOperations(A, B, C)
// </vc-spec>
// <vc-code>
{
  Lemma_ValidInputBounds(A, B, C);
  Lemma_SortDescendingPreservesValidInput(A, B, C);
  Lemma_SortDescendingOrder(A, B, C);
  
  var sorted := SortDescending(A, B, C);
  var a0 := sorted.0;
  var a1 := sorted.1;
  var a2 := sorted.2;
  
  var count := 0;
  
  while a0 != a1 || a0 != a2 || a1 != a2
    invariant 0 <= a0 <= 50 && 0 <= a1 <= 50 && 0 <= a2 <= 50
    invariant a0 >= a1 >= a2
    invariant ValidInput(a0, a1, a2)
    invariant count <= 2 * (a0 - a2)
    decreases 3*(a0 - a2) + 2*(a0 - a1) + (a1 - a2)
  {
    // Sort descending
    if a0 < a1 { a0, a1 := a1, a0; }
    if a0 < a2 { a0, a2 := a2, a0; }
    if a1 < a2 { a1, a2 := a2, a1; }
    
    if a0 == a1 {
      a2 := a2 + 1;
    } else if a1 == a2 {
      a1 := a1 + 1;
      a2 := a2 + 1;
    } else {
      a2 := a2 + 2;
    }
    count := count + 1;
    
    // Sort again after updates
    if a0 < a1 { a0, a1 := a1, a0; }
    if a0 < a2 { a0, a2 := a2, a0; }
    if a1 < a2 { a1, a2 := a2, a1; }
  }
  
  assert a0 == a1 && a1 == a2;
  assert count == MinOperations(A, B, C);
  result := count;
}
// </vc-code>

