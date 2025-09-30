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
function mapI(i: int, j: int, k: int, n: int): int
  requires 0 <= i < n && 0 <= j < n && n > 0
  {
    var kn := normalizeK(k);
    if kn == 0 then i
    else if kn == 1 then j
    else if kn == 2 then n - 1 - i
    else n - 1 - j
  }

function mapJ(i: int, j: int, k: int, n: int): int
  requires 0 <= i < n && 0 <= j < n && n > 0
  {
    var kn := normalizeK(k);
    if kn == 0 then j
    else if kn == 1 then n - 1 - i
    else if kn == 2 then n - 1 - j
    else i
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
  var n := m.Length0;
  var k_normalized := normalizeK(k);
  result := new real[n, n];

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < n ==> result[mapI(ii, jj, k_normalized, n), mapJ(ii, jj, k_normalized, n)] == m[ii, jj]
  {
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant forall jj0 :: 0 <= jj0 < j ==> result[mapI(i, jj0, k_normalized, n), mapJ(i, jj0, k_normalized, n)] == m[i, jj0]
      invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < n ==> result[mapI(ii, jj, k_normalized, n), mapJ(ii, jj, k_normalized, n)] == m[ii, jj]
    {
      var ti := mapI(i, j, k_normalized, n);
      var tj := mapJ(i, j, k_normalized, n);
      result[ti, tj] := m[i, j];
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
