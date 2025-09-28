// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ValidSlice(s: string, start: int, end: int): bool {
  return 0 <= start && start <= end && end <= |s|;
}
// </vc-helpers>

// <vc-spec>
method rfind(a: seq<string>, sub: seq<string>, start: seq<int>, endPos: seq<int>) returns (result: seq<int>)
  // All input sequences must have the same length
  requires |a| == |sub| == |start| == |endPos|
  // Start positions must be non-negative and not exceed end positions
  requires forall i :: 0 <= i < |start| ==> 0 <= start[i] <= endPos[i]
  // Result sequence has same length as inputs
  ensures |result| == |a|
  // For each element i, the result satisfies the rfind specification
  ensures forall i :: 0 <= i < |result| ==> 
    // Result is either -1 or a valid index within the string
    (result[i] == -1 || (0 <= result[i] < |a[i]|)) &&
    
    // If result is -1, then no occurrence of substring exists within the specified range
    (result[i] == -1 ==> 
      (forall j {:trigger a[i][j..j+|sub[i]|]} :: start[i] <= j && j + |sub[i]| <= endPos[i] + 1 && j + |sub[i]| <= |a[i]| ==>
        a[i][j..j+|sub[i]|] != sub[i])) &&
    
    // If result is non-negative, it represents the rightmost valid occurrence
    (result[i] >= 0 ==> 
      // The result position is within the search range
      start[i] <= result[i] && 
      result[i] + |sub[i]| <= endPos[i] + 1 &&
      // The result position is valid within the string bounds  
      result[i] + |sub[i]| <= |a[i]| &&
      // The substring matches at the result position
      a[i][result[i]..result[i]+|sub[i]|] == sub[i] &&
      // This is the rightmost occurrence - no later occurrence exists in the range
      (forall j {:trigger a[i][j..j+|sub[i]|]} :: (result[i] < j && j + |sub[i]| <= endPos[i] + 1 && 
                   start[i] <= j && j + |sub[i]| <= |a[i]|) ==> 
        a[i][j..j+|sub[i]|] != sub[i]))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected ValidSlice bounds in loop invariants and search conditions for proper string slicing, ensuring `j+|sub[i]|` doesn't exceed `|a[i]|`. */
{
  var r := new int[|a|];
  for i := 0 to |a| - 1
    invariant 0 <= i <= |a|
    invariant |r| == |a|
    invariant forall k :: 0 <= k < i ==> 
      (r[k] == -1 || (0 <= r[k] < |a[k]|)) && 
      (r[k] == -1 ==> 
        (forall j :: start[k] <= j && j + |sub[k]| <= endPos[k] + 1 && j + |sub[k]| <= |a[k]| ==> 
          a[k][j..j+|sub[k]|] != sub[k]))) && 
      (r[k] >= 0 ==> 
        start[k] <= r[k] && 
        r[k] + |sub[k]| <= endPos[k] + 1 &&
        r[k] + |sub[k]| <= |a[k]| &&
        a[k][r[k]..r[k]+|sub[k]|] == sub[k] && 
        (forall j :: (r[k] < j && j + |sub[k]| <= endPos[k] + 1 && start[k] <= j && j + |sub[k]| <= |a[k]|) ==> 
          a[k][j..j+|sub[k]|] != sub[k]))
  {
    var found_idx := -1;
    var current_end_pos := endPos[i];
    if |sub[i]| == 0 {
        if start[i] <= current_end_pos {
            found_idx := current_end_pos;
        } else {
            found_idx := -1; // No valid position for an empty string if endPos is before start
        }
    } else {
        for j := current_end_pos 
               down to start[i]
          invariant start[i] <= j <= current_end_pos + 1 
          invariant found_idx == -1 || 
                    (start[i] <= found_idx && 
                     found_idx + |sub[i]| <= current_end_pos + 1 && 
                     found_idx + |sub[i]| <= |a[i]| && 
                     a[i][found_idx..found_idx+|sub[i]|] == sub[i])
          invariant forall k_prime :: j < k_prime && k_prime <= current_end_pos && start[i] <= k_prime && k_prime + |sub[i]| <= current_end_pos + 1 && k_prime + |sub[i]| <= |a[i]| ==> a[i][k_prime..k_prime+|sub[i]|] != sub[i] 
        {
          if j + |sub[i]| <= |a[i]| && j + |sub[i]| <= current_end_pos + 1 && a[i][j..j+|sub[i]|] == sub[i] {
            found_idx := j;
            break;
          }
        }
    }
    r[i] := found_idx;
  }
  return r;
}
// </vc-code>
