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
  requires a0 + a1 + a2 <= 150  // Due to ValidInput constraint
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
  // Base case - all equal
  if a0 == a1 && a1 == a2 {
    assert MinOperations(a0, a1, a2) == 0;
  }
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
  var a0 := A;
  var a1 := B;
  var a2 := C;
  
  var count := 0;
  
  while a0 != a1 || a0 != a2 || a1 != a2
    invariant 0 <= a0 <= 50 + count && 0 <= a1 <= 50 + count && 0 <= a2 <= 50 + count
    invariant a0 + a1 + a2 <= 150 + 3 * count
    invariant count <= 2 * (a0 - a2)  // Upper bound
    decreases a0 - a2 + a0 - a1  // Decreasing measure
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
  
  result := count;
}
// </vc-code>

