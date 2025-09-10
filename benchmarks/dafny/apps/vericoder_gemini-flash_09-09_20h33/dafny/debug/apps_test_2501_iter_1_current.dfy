predicate ValidInput(A: array<int>)
  reads A
{
  A.Length >= 2 && forall i :: 0 <= i < A.Length ==> A[i] >= 1
}

function abs(x: int): int
{
  if x >= 0 then x else -x
}

predicate ValidPair(A: array<int>, i: int, j: int)
  reads A
  requires 0 <= i < A.Length && 0 <= j < A.Length
{
  i != j && abs((i+1) - (j+1)) == A[i] + A[j]
}

function CountValidPairs(A: array<int>): int
  reads A
  requires ValidInput(A)
{
  |set i, j | 0 <= i < A.Length && 0 <= j < A.Length && ValidPair(A, i, j) :: (i, j)|
}

// <vc-helpers>
predicate PairExists(A: array<int>, i: int, j: int)
  reads A
  requires 0 <= i < A.Length && 0 <= j < A.Length
{
  ValidPair(A, i, j)
}
// </vc-helpers>

// <vc-spec>
method solve(A: array<int>) returns (result: int)
  requires ValidInput(A)
  ensures result >= 0
  ensures result == CountValidPairs(A)
// </vc-spec>
// <vc-code>
{
  var count := 0;
  var n := A.Length;

  // We iterate through all possible pairs (i, j) where i < j
  // and check if ValidPair(A, i, j) holds.
  // Since ValidPair(A, i, j) is symmetric for the condition abs((i+1) - (j+1)) == A[i] + A[j]
  // and the definition of CountValidPairs counts ordered pairs (i, j) where i != j,
  // we count (i, j) and (j, i) if ValidPair(A, i, j) holds.
  //
  // Specifically, if ValidPair(A, i, j) holds, then:
  // - If i < j, we count (i, j) and (j, i).
  //
  // Let P be the set of pairs counted by CountValidPairs:
  // P = {(i, j) | 0 <= i < A.Length && 0 <= j < A.Length && ValidPair(A, i, j)}
  //
  // Our loop iterates over i from 0 to n-1 and j from i+1 to n-1.
  // For each such pair (i, j) with i < j, if ValidPair(A, i, j) is true,
  // we increment count by 2, accounting for both (i, j) and (j, i).
  //
  // Loop invariant:
  // `count` stores the number of valid pairs (x, y) where x < y
  // and either x < i OR (x == i AND y < j)
  //
  // More precisely:
  // `count` is the number of pairs (p, q) such that:
  //   0 <= p < A.Length && 0 <= q < A.Length && p != q && ValidPair(A, p, q)
  //   AND (p < i OR (p == i && q < j))
  //
  // This invariant needs to be carefully formulated for the nested loop.
  // Let's reformulate.
  //
  // Outer loop invariant for `i`:
  // `count` stores the total number of valid pairs (x, y) such that:
  //   0 <= x < A.Length && 0 <= y < A.Length && x != y && ValidPair(A, x, y)
  //   AND (x < i)
  //   This isn't quite right as it doesn't account for pairs with x=i.
  //
  // Let's use a simpler invariant:
  // `count` stores the number of pairs (x, y) such that:
  //   0 <= x < A.Length && 0 <= y < A.Length && x != y && ValidPair(A, x, y)
  //   AND (x < i || (x == i && y < j_outer_loop_value))
  // where j_outer_loop_value is the value of j when the outer loop completes that iteration.
  //
  // A better invariant for the outer loop at the start of iteration `i`:
  // `count` == |{(p,q) | 0 <= p < A.Length && 0 <= q < A.Length && p != q && ValidPair(A,p,q) && p < i}|
  // This is simpler.
  //
  // After the inner loop for a given `i` finishes, `count` will have also cumulatively added
  // all pairs (i, j) and (j, i) where `j` iterated from `i+1` to `n-1`.

  var i := 0;
  while i < n {
    invariant 0 <= i <= n;
    invariant count == |set p, q | 0 <= p < A.Length && 0 <= q < A.Length && p != q && ValidPair(A, p, q) && p < i :: (p, q)|;

    var j := i + 1;
    while j < n {
      invariant i < j <= n;
      invariant count == (|set p, q | 0 <= p < A.Length && 0 <= q < A.Length && p != q && ValidPair(A, p, q) && p < i :: (p, q)|) +
                        (|set p, q | (p == i && i < q < j && ValidPair(A, i, q)) || (q == i && i < p < j && ValidPair(A, p, i)) :: (p, q)|);
      
      if ValidPair(A, i, j) {
        count := count + 2; // Account for (i, j) and (j, i)
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  result := count;
}
// </vc-code>

