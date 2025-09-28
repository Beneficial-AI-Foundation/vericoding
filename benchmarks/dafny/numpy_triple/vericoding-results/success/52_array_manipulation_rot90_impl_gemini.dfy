// <vc-preamble>
// Helper function to compute normalized k value (k mod 4, always non-negative)
function normalizeK(k: int): int
{
    var k_mod := k % 4;
    if k_mod < 0 then k_mod + 4 else k_mod
}

// Method to rotate a square 2D matrix by 90 degrees counterclockwise k times
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [Added 'reads m' to function signature to fix compilation errors.] */
function rotatedValue(m: array2<real>, n: int, i: int, j: int, k_normalized: int): real
  reads m
  requires m.Length0 == n && m.Length1 == n
  requires n > 0
  requires 0 <= i < n && 0 <= j < n
  requires 0 <= k_normalized < 4
{
  if k_normalized == 0 then m[i, j]
  else if k_normalized == 1 then m[n - 1 - j, i]
  else if k_normalized == 2 then m[n - 1 - i, n - 1 - j]
  else m[j, n - 1 - i]
}
// </vc-helpers>

// <vc-spec>
method rot90(m: array2<real>, k: int) returns (result: array2<real>)
    // Preconditions: matrix must be square and non-empty
    requires m.Length0 == m.Length1
    requires m.Length0 > 0
    
    // Postconditions: result has same dimensions as input
    ensures result.Length0 == m.Length0
    ensures result.Length1 == m.Length1
    
    // Main rotation specification based on normalized k value
    ensures var n := m.Length0;
            var k_normalized := normalizeK(k);
            
            // Case 0: No rotation (identity transformation)
            (k_normalized == 0 ==> 
                forall i, j :: 0 <= i < n && 0 <= j < n ==> 
                    result[i, j] == m[i, j]) &&
            
            // Case 1: 90 degrees counterclockwise - (i,j) maps to (j, n-1-i)
            (k_normalized == 1 ==> 
                forall i, j :: 0 <= i < n && 0 <= j < n ==> 
                    result[j, n-1-i] == m[i, j]) &&
            
            // Case 2: 180 degrees - (i,j) maps to (n-1-i, n-1-j)
            (k_normalized == 2 ==> 
                forall i, j :: 0 <= i < n && 0 <= j < n ==> 
                    result[n-1-i, n-1-j] == m[i, j]) &&
            
            // Case 3: 270 degrees counterclockwise - (i,j) maps to (n-1-j, i)
            (k_normalized == 3 ==> 
                forall i, j :: 0 <= i < n && 0 <= j < n ==> 
                    result[n-1-j, i] == m[i, j])
    
    // Sanity check: corner element rotation for k=1 case
    ensures var n := m.Length0;
            var k_normalized := normalizeK(k);
            k_normalized == 1 && n >= 2 ==> 
                result[0, n-1] == m[0, 0]
    
    // Sanity check: center element preservation for 180 degree rotation of odd-sized matrix
    ensures var n := m.Length0;
            var k_normalized := normalizeK(k);
            k_normalized == 2 && n % 2 == 1 ==> 
                var center := n / 2;
                result[center, center] == m[center, center]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): [Strengthened inner loop invariant to fix invariant violation.] */
  var n := m.Length0;
  var k_normalized := normalizeK(k);
  
  result := new real[n, n];
  
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length0 == n && result.Length1 == n
    invariant forall r, c :: 0 <= r < i && 0 <= c < n ==> result[r, c] == rotatedValue(m, n, r, c, k_normalized)
  {
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      // Preserve the outer loop invariant for rows r < i
      invariant forall r, c :: 0 <= r < i && 0 <= c < n ==> result[r, c] == rotatedValue(m, n, r, c, k_normalized)
      // Show progress for the current row i
      invariant forall c :: 0 <= c < j ==> result[i, c] == rotatedValue(m, n, i, c, k_normalized)
    {
       result[i,j] := rotatedValue(m, n, i, j, k_normalized);
       j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
