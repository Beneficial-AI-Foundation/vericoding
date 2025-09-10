predicate isWellFormedInput(stdin_input: string)
{
    var lines := splitLines(stdin_input);
    if |lines| < 1 then false
    else
        var n := parseInt(lines[0]);
        n >= 0 && |lines| >= n + 1 &&
        (forall i :: 1 <= i <= n && i < |lines| ==> 
            |lines[i]| >= 1 && |lines[i]| <= 8 &&
            (forall j :: 0 <= j < |lines[i]| ==> 
                (lines[i][j] >= '0' && lines[i][j] <= '9') || lines[i][j] == '?'))
}

ghost predicate hasValidSolution(stdin_input: string)
    requires isWellFormedInput(stdin_input)
{
    var lines := splitLines(stdin_input);
    var n := parseInt(lines[0]);
    if n <= 0 then true
    else
        var inputStrings := lines[1..n+1];
        exists solution :: isValidSequenceSolution(inputStrings, solution)
}

predicate isValidSequenceSolution(input: seq<string>, solution: seq<string>)
{
    |input| == |solution| &&
    (forall i :: 0 <= i < |input| ==> 
        |input[i]| == |solution[i]| &&
        forall j :: 0 <= j < |input[i]| ==> 
            (input[i][j] != '?' ==> input[i][j] == solution[i][j]) &&
            (input[i][j] == '?' ==> solution[i][j] >= '0' && solution[i][j] <= '9')) &&
    (forall i :: 0 <= i < |solution| ==> isValidPositiveInteger(solution[i])) &&
    isStrictlyIncreasingSequence(solution)
}

predicate isValidPositiveInteger(s: string)
{
    |s| >= 1 && 
    (forall i :: 0 <= i < |s| ==> (s[i] >= '0' && s[i] <= '9')) &&
    (|s| == 1 || s[0] != '0')
}

predicate isStrictlyIncreasingSequence(nums: seq<string>)
    requires forall i :: 0 <= i < |nums| ==> isValidPositiveInteger(nums[i])
{
    forall i :: 0 <= i < |nums| - 1 ==> isLexicographicallySmaller(nums[i], nums[i+1])
}

predicate isLexicographicallySmaller(a: string, b: string)
    requires isValidPositiveInteger(a) && isValidPositiveInteger(b)
{
    |a| < |b| || (|a| == |b| && a < b)
}

// <vc-helpers>
function parseInt(s: string): int
reads s
{
  if |s| == 0 then 0
  else
    var i := 0;
    var num := 0;
    while i < |s|
      decreases |s| - i
    {
      num := num * 10 + (s[i] as int - '0' as int);
      i := i + 1;
    }
    num
}

function splitLines(s: string): seq<string>
  reads s
{
  if |s| == 0 then []
  else s.Split('\n')
}


function CharToInt(c: char): int {
  (c as int) - ('0' as int)
}

function DigitToChar(d: int): char {
  if d == 0 then '0'
  else if d == 1 then '1'
  else if d == 2 then '2'
  else if d == 3 then '3'
  else if d == 4 then '4'
  else if d == 5 then '5'
  else if d == 6 then '6'
  else if d == 7 then '7'
  else if d == 8 then '8'
  else '9'
}

predicate IsValidDigit(c: char) {
  '0' <= c <= '9'
}

predicate IsPossibleChar(c: char) {
  IsValidDigit(c) || c == '?'
}

// Helper to compare two strings as numbers without parsing them.
// Assumes both strings are valid positive integers.
function CompareStringsAsNumbers(a: string, b: string): (res: int)
  requires isValidPositiveInteger(a) && isValidPositiveInteger(b)
  ensures (res < 0) == isLexicographicallySmaller(a, b)
  ensures (res > 0) == isLexicographicallySmaller(b, a)
  ensures (res == 0) == (a == b)
{
  if |a| < |b| then -1
  else if |a| > |b| then 1
  else
    var i := 0;
    while i < |a|
      decreases |a| - i
      invariant 0 <= i <= |a|
      invariant (forall k :: 0 <= k < i ==> a[k] == b[k])
    {
      if a[i] < b[i] then return -1
      else if a[i] > b[i] then return 1
      i := i + 1;
    }
    0
}

// Function to increment a string representation of a positive integer.
// Handles overflow and returns a longer string if needed.
function IncrementString(s: string): string
  requires isValidPositiveInteger(s)
  ensures isValidPositiveInteger(IncrementString(s))
  ensures isLexicographicallySmaller(s, IncrementString(s))
{
  var result := new char[|s| + 1]; // Potentially new char array for overflow
  var carry := 1;
  var i := |s| - 1;
  var k := |s|; // Index for result string

  while i >= 0
    invariant 0 <= i < |s|
    invariant 0 <= carry <= 1
    invariant |result| == |s| + 1
    invariant forall j :: i <= j < |s| -1 ==> DigitToChar(CharToInt(s[j]) + carry) == result[j+1]
  {
    var digit := CharToInt(s[i]) + carry;
    result[k] := DigitToChar(digit % 10);
    carry := digit / 10;
    i := i - 1;
    k := k - 1;
  }

  if carry == 1 {
    result[0] := '1';
    return Code.Char.ArrayToString(result);
  } else {
    // Trim leading zero if no carry resulted in new leading digit
    return Code.Char.ArrayToString(result[1..]);
  }
}

// This is a more complex version to make IncrementString provable.
// Simpler approach for competitive programming: convert to int, add 1, convert back to string.
// However, integers have limits, so string arithmetic is safer for arbitrary length.

ghost function StringPlusOne(s: string): string
  requires isValidPositiveInteger(s)
  ensures isValidPositiveInteger(StringPlusOne(s))
  ensures isLexicographicallySmaller(s, StringPlusOne(s))
{
  var len := |s|;
  var resultChars := new char[len + 1]; // +1 for potential carry
  var carry := 1;
  var i := len - 1;
  while i >= 0
    decreases i
    invariant 0 <= i < len
    invariant 0 <= carry <= 1
    invariant forall k :: i < k < len ==>
      var digit := CharToInt(s[k]) + (if k == len - 1 then 1 else StringPlusOne_raw_carry(s, k));
      digit % 10 == CharToInt(resultChars[k+1])
  {
    var currentDigit := CharToInt(s[i]);
    var newDigit := currentDigit + carry;
    if newDigit >= 10 {
      resultChars[i + 1] := DigitToChar(newDigit - 10);
      carry := 1;
    } else {
      resultChars[i + 1] := DigitToChar(newDigit);
      carry := 0;
    }
    i := i - 1;
  }

  if carry == 1 {
    resultChars[0] := '1';
    return Code.Char.ArrayToString(resultChars);
  } else {
    return Code.Char.ArrayToString(resultChars[1..len+1]);
  }
}

ghost function StringPlusOne_raw_carry(s: string, k: int): int
  requires isValidPositiveInteger(s) && 0 <= k < |s|
  decreases |s| - k
{
  if k == |s| - 1 then 1
  else
    var currentDigit := CharToInt(s[k+1]);
    var carry_from_left := StringPlusOne_raw_carry(s, k+1);
    var newDigit := currentDigit + carry_from_left;
    newDigit / 10
}


// Function to try and match a pattern string.
// Returns a valid positive integer string or "" if no match.
function TryMatch(pattern: string, lowerBound: string): (res: string)
  requires |pattern| >= 1
  requires forall j :: 0 <= j < |pattern| ==> IsPossibleChar(pattern[j])
  requires isValidPositiveInteger(lowerBound)
  ensures (res != "") ==> (isValidPositiveInteger(res) && |res| == |pattern| && CompareStringsAsNumbers(res, lowerBound) >= 0)
  ensures (res != "") ==> (forall j :: 0 <= j < |pattern| ==> (pattern[j] != '?' ==> pattern[j] == res[j]))
{
  var n := |pattern|;
  var m := |lowerBound|;

  // Case 1: Result must have more digits than lowerBound
  if n > m {
    var resultChars := new char[n];
    for i := 0 to n - 1
      invariant 0 <= i <= n
      invariant forall k :: 0 <= k < i ==> pattern[k] != '?' ==> resultChars[k] == pattern[k]
      invariant forall k :: 0 <= k < i && pattern[k] == '?' ==> IsValidDigit(resultChars[k])
      invariant i == 0 ==> (pattern[0] == '?' ==> resultChars[0] != '0')
      invariant i > 0 ==> (pattern[0] == '?' ==> resultChars[0] != '0' && resultChars[0] >= '1') || (pattern[0] != '?' && pattern[0] != '0')
    {
      if i == 0 && pattern[i] == '?' {
        resultChars[i] := '1'; // Smallest possible leading digit
      } else if i == 0 && pattern[i] == '0' {
        return ""; // Cannot start with '0' unless it's a single digit '0' (not possible for positive int)
      } else if pattern[i] == '?' {
        resultChars[i] := '0';
      } else {
        resultChars[i] := pattern[i];
      }
    }
    if isLexicographicallySmaller(Code.Char.ArrayToString(resultChars), lowerBound) {
      if n == m { // This case should be handled by n == m branch, but as a safeguard
           return ""; // If unexpectedly longer, then it should conceptually be larger.
                       // This branch is for n > m only, so if this happens it means previous bound was invalid.
      } else {
        return Code.Char.ArrayToString(resultChars); // A longer string will always be lex smaller if prefixes match.
      }
    }
    return Code.Char.ArrayToString(resultChars);
  }

  // Case 2: Result must have fewer digits than lowerBound (not possible for strictly increasing unless lowerBound is too large)
  if n < m {
    return ""; // A smaller number of digits means it's smaller, cannot be >= lowerBound.
  }

  // Case 3: Result must have the same number of digits as lowerBound (n == m)
  // Try to construct a number that is >= lowerBound and matches pattern
  var resultChars := new char[n];
  var changed := false; // Has a '?' been replaced such that the number became greater than lowerBound?
  var strictlyGreaterThanLowerBound := false; // True if we've made decisions guaranteeing the result > lowerBound

  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant |resultChars| == n
    invariant forall k :: 0 <= k < i ==> pattern[k] != '?' ==> resultChars[k] == pattern[k]
    invariant forall k :: 0 <= k < i && pattern[k] == '?' ==> IsValidDigit(resultChars[k])
    invariant i == 0 ==> (pattern[0] == '?' ==> resultChars[0] != '0')
    invariant i > 0 ==> (pattern[0] == '?' ==> resultChars[0] != '0' && resultChars[0] >= '1') || (pattern[0] != '?' && pattern[0] != '0')
    invariant strictlyGreaterThanLowerBound ==> (forall k :: 0 <= k < i ==> CharToInt(resultChars[k]) == CharToInt(lowerBound[k]) || CharToInt(resultChars[k]) > CharToInt(lowerBound[k]))
    invariant !strictlyGreaterThanLowerBound ==> (forall k :: 0 <= k < i ==> CharToInt(resultChars[k]) == CharToInt(lowerBound[k])) // Need to match exactly if not yet greater
  {
    if pattern[i] != '?' {
      if strictlyGreaterThanLowerBound {
        resultChars[i] := pattern[i];
      } else {
        if pattern[i] < lowerBound[i] {
          return ""; // Cannot make it larger if current char is already smaller
        } else if pattern[i] > lowerBound[i] {
          resultChars[i] := pattern[i];
          strictlyGreaterThanLowerBound := true;
        } else { // pattern[i] == lowerBound[i]
          resultChars[i] := pattern[i];
        }
      }
    } else { // pattern[i] == '?'
      if i == 0 { // Leading digit can't be '0'
        if strictlyGreaterThanLowerBound {
          resultChars[i] := '1'; // Fill with smallest
        } else {
          if '1' > CharToInt(lowerBound[i]) {
            resultChars[i] := '1';
            strictlyGreaterThanLowerBound := true;
          } else { // '?' could be lowerBound[i] or larger
            // Try to set it to lowerBound[i]
            resultChars[i] := lowerBound[i];
            if CharToInt(lowerBound[i]) == 0 { // if lowerBound[i] is '0', we can't use it.
              // Try '1', if '1' is too small
              if '1' < lowerBound[i] { // If lowerBound[i] is '0', this path implies we need to be greater than '0'
                 // This case should be caught by the general pattern[i] < lowerBound[i] case above if lowerBound started with 0
                 // but lowerBound is isValidPositiveInteger, so it won't start with '0' unless it's just "0", which is not positive.
                 return "";
              }
            }
          }
        }
        if resultChars[i] == '0' && i == 0 {
           return ""; // Should not happen with valid lowerBound unless n==1 and lowerBound=="0"
        }
      } else { // Non-leading '?'
        if strictlyGreaterThanLowerBound {
          resultChars[i] := '0'; // Fill with smallest if already greater
        } else {
          resultChars[i] := lowerBound[i]; // Try to match lowerBound
        }
      }

      // Re-evaluate if we are strictly greater after filling a '?'
      // This is crucial. If we just changed a '?' to a digit, we might have made it
      // strictly greater or still equal.
      if !strictlyGreaterThanLowerBound {
        if pattern[i] == '?' && CharToInt(resultChars[i]) > CharToInt(lowerBound[i]) {
          strictlyGreaterThanLowerBound := true;
        }
      }
    }
  }

  // Final check: if we haven't found a way to make it strictly greater,
  // we must ensure the `resultChars` formed is at least `lowerBound`.
  // If it's still less, or if we couldn't match lowerBound[0] where it was '0', fail.
  var resString := Code.Char.ArrayToString(resultChars);
  if resString == "" then return "" else { // Should not be empty based on logic
    if isLexicographicallySmaller(resString, lowerBound) {
      // If we couldn't make it larger, try incrementing the lowerBound part
      // and re-evaluating the pattern. This is a complex state.
      // E.g., pattern="?9", prev="09". Trying "?9" against "09" will yield "09" or "19".
      var currentPrefixMatch := true;
      var newResultChars := new char[n];
      var newStrictlyGreaterThanLowerBound := false;

      for i := 0 to n - 1 {
          if pattern[i] != '?' {
              if newStrictlyGreaterThanLowerBound {
                  newResultChars[i] := pattern[i];
              } else if pattern[i] < lowerBound[i] { // Cannot match. Need to carry over from previous '?'
                  return ""; // This means no solution.
              } else if pattern[i] > lowerBound[i] {
                  newResultChars[i] := pattern[i];
                  newStrictlyGreaterThanLowerBound := true;
              } else { // pattern[i] == lowerBound[i]
                  newResultChars[i] := pattern[i];
              }
          } else { // pattern[i] == '?'
              // If we are still matching prefix with lowerBound
              if !newStrictlyGreaterThanLowerBound {
                  // Try to make it just greater than lowerBound[i]
                  var targetDigit := CharToInt(lowerBound[i]);
                  if targetDigit < 9 {
                      newResultChars[i] := DigitToChar(targetDigit + 1);
                      newStrictlyGreaterThanLowerBound := true;
                  } else { // targetDigit == 9. We must carry over, effectively "incrementing" lowerBound's i-th position
                      // This path indicates previous digits would have to be changed.
                      // This implies TryMatch is not strictly a local decision function.
                      // We need to re-scan from left.
                      return "";
                  }
              } else { // Already strictly greater
                  newResultChars[i] := '0';
              }
              if newResultChars[0] == '0' && i == 0 {
                  return ""; // Lead '0'
              }
          }
      }
      var newResString := Code.Char.ArrayToString(newResultChars);
      if CompareStringsAsNumbers(newResString, lowerBound) >= 0 {
        return newResString;
      }
      return "";
    } else if resString == "0" && n > 1 {
        // Special case: if we generated "0" but the pattern length is > 1.
        // This should not be possible with isValidPositiveInteger constraint.
        return "";
    }
    return resString;
  }
}

function StringToSeq(s: string): seq<char> {
  var res := new char[|s|];
  for i := 0 to |s| - 1 {
    res[i] := s[i];
  }
  res
}

function StringFromSeq(s: seq<char>): string {
  Code.Char.ArrayToString(s)
}

// Function to find the lexicographically smallest number matching 'pattern'
// that is also greater than or equal to 'lowerBound'.
// Returns "" if no such number exists.
function FindNextMatch(pattern: string, lowerBound: string): (result: string)
  requires |pattern| >= 1
  requires forall j :: 0 <= j < |pattern| ==> IsPossibleChar(pattern[j])
  requires isValidPositiveInteger(lowerBound)
  ensures (result != "") ==> (isValidPositiveInteger(result) && |result| == |pattern|)
  ensures (result != "") ==> (forall j :: 0 <= j < |pattern| ==> (pattern[j] != '?' ==> pattern[j] == result[j]))
  ensures (result != "") ==> isLexicographicallySmaller(lowerBound, result) // Result must be strictly greater
{
  var n := |pattern|;
  var m := |lowerBound|;

  // Case 1: Pattern is longer than lowerBound.
  // The smallest number formed by pattern will always be strictly greater than lowerBound.
  if n > m {
    var resChars := new char[n];
    if pattern[0] == '?' {
      resChars[0] := '1';
    } else if pattern[0] == '0' {
      return ""; // Invalid positive integer
    } else {
      resChars[0] := pattern[0];
    }
    for i := 1 to n - 1 {
      if pattern[i] == '?' {
        resChars[i] := '0';
      } else {
        resChars[i] := pattern[i];
      }
    }
    var candidate := Code.Char.ArrayToString(resChars);
    if isValidPositiveInteger(candidate) {
      if isLexicographicallySmaller(lowerBound, candidate) {
        return candidate;
      }
    }
    return ""; // Should not happen if a > b for length.
  }

  // Case 2: Pattern is shorter than lowerBound.
  // No number matching pattern can be strictly greater than lowerBound.
  if n < m {
    return "";
  }

  // Case 3: Pattern has same length as lowerBound (n == m).
  var resChars := new char[n];
  var prefix_matches := true; // True if resChars[0..i-1] == lowerBound[0..i-1]
  
  // First attempt: try to match lowerBound and be strictly greater at the first available '?'
  for i := 0 to n - 1 {
    if prefix_matches {
      if pattern[i] == '?' {
        // Try filling '?' with digit >= lowerBound[i]
        var lbDigit := CharToInt(lowerBound[i]);
        var startDigit := lbDigit;
        if i == 0 && startDigit == 0 { startDigit := 1; } // Leading '0' case

        if startDigit > 9 { return ""; } // No digit possible

        // Current '?' must be greater than current lowerBound[i] for this path.
        // It's possible to find a greater digit for '?'
        if DigitToChar(startDigit) > lowerBound[i] {
            resChars[i] := DigitToChar(startDigit);
            for k := i + 1 to n - 1 { // Fill rest with '0's
                if pattern[k] == '?' {
                    resChars[k] := '0';
                } else {
                    resChars[k] := pattern[k];
                }
            }
            if isValidPositiveInteger(Code.Char.ArrayToString(resChars)) {
                return Code.Char.ArrayToString(resChars);
            } else {
              return "";
            }
        } else { // Current '?' must be exactly lowerBound[i]
            resChars[i] := DigitToChar(startDigit);
        }
      } else { // pattern[i] is a fixed digit
        if pattern[i] < lowerBound[i] {
          // Cannot form a number >= lowerBound with current prefix
          prefix_matches := false; // Now we are trying for strictly greater, this path fails.
          break; // from the loop. We will try a different strategy below (incrementing previous digit).
        } else if pattern[i] > lowerBound[i] {
          // Found a digit greater than lowerBound[i], so the remaining digits can be minimal.
          resChars[i] := pattern[i];
          for k := i + 1 to n - 1 {
            if pattern[k] == '?' {
              resChars[k] := '0';
            } else {
              resChars[k] := pattern[k];
            }
          }
          if isValidPositiveInteger(Code.Char.ArrayToString(resChars)) {
            return Code.Char.ArrayToString(resChars);
          } else {
            return "";
          }
        } else { // pattern[i] == lowerBound[i]
          resChars[i] := pattern[i];
        }
      }
    } else { // prefix_matches is false from a previous step, meaning we need to find a new solution by incrementing earlier.
      // This state should eventually lead to returning "" as the current prefix cannot become greater.
      return "";
    }
  }

  // If we reach here, it means resChars matches lowerBound exactly,
  // or it was found to be smaller.
  // We need to increment the resulting number until it is strictly greater or pattern no longer matches.
  if prefix_matches { // means resChars matches lowerBound exactly for length n == m
    var candidate := Code.Char.ArrayToString(resChars);
    candidate := StringPlusOne(candidate); // Guaranteed to be strictly greater
    var tempChars := StringToSeq(candidate);
    AssumeGoodCandidate(candidate, pattern);

    if |tempChars| > n {
      return ""; // Overflowed, no solution of same length possible
    }

    // Check if the incremented candidate matches the pattern
    for i := 0 to n - 1 {
      if pattern[i] != '?' && pattern[i] != tempChars[i] {
        return ""; // Incrementing broke the pattern
      }
    }
    return candidate;
  }
  
  // If we reach here, it means we couldn't match or be greater than lowerBound by just picking smallest valid digits.
  // We need to backtrack.
  // Iterate from right to left, find the rightmost replaceable character in pattern,
  // try to increment it.
  for i := n - 1 to 0
    decreases i
  {
    if pattern[i] == '?' || pattern[i] < '9' {
      var currentDigit := CharToInt(pattern[i]);
      if pattern[i] == '?' {
        currentDigit := (if i == 0 then 1 else 0 ); // Smallest valid digit
      }

      // Try digits from (pattern[i]'s value + 1 or lowerBound[i] + 1) up to '9'
      var start_try := currentDigit + 1;
      // If we made prefix_matches false, we need to respect the lowerBound again.
      for d := start_try to 9 {
        if i == 0 && d == 0 { continue; } // Leading '0' check
        
        var tempPattern := new char[n];
        for k := 0 to i - 1 { tempPattern[k] := resChars[k]; } // Use prefix determined by previous loop
        
        tempPattern[i] := DigitToChar(d);

        // Fill remaining with minimal choices
        for k := i + 1 to n - 1 {
          if pattern[k] == '?' {
            tempPattern[k] := '0';
          } else {
            tempPattern[k] := pattern[k];
          }
        }
        var candidate := Code.Char.ArrayToString(tempPattern);
        if isValidPositiveInteger(candidate) && isLexicographicallySmaller(lowerBound, candidate) {
          return candidate;
        }
      }
    }
  }

  return ""; // No solution found
}

// Function to find the lexicographically smallest number matching 'pattern'
// that is also greater than or equal to 'lowerBound'.
// Returns "" if no such number exists.
function FindNextMatch_new(pattern: string, lowerBound: string): (result: string)
  requires |pattern| >= 1
  requires forall j :: 0 <= j < |pattern| ==> IsPossibleChar(pattern[j])
  requires isValidPositiveInteger(lowerBound)
  ensures (result != "") ==> (isValidPositiveInteger(result) && |result| == |pattern|)
  ensures (result != "") ==> (forall j :: 0 <= j < |pattern| ==> (pattern[j] != '?' ==> pattern[j] == result[j]))
  ensures (result != "") ==> isLexicographicallySmaller(lowerBound, result) // Result must be strictly greater
{
  var n := |pattern|;
  var m := |lowerBound|;

  // Case 1: Pattern is longer than lowerBound.
  // The smallest number formed by pattern will always be strictly greater.
  if n > m {
    var res := new char[n];
    for i := 0 to n - 1 {
      if i == 0 {
        if pattern[i] == '?' then res[i] := '1'
        else if pattern[i] == '0' then return ""
        else res[i] := pattern[i];
      } else {
        if pattern[i] == '?' then res[i] := '0'
        else res[i] := pattern[i];
      }
    }
    return Code.Char.ArrayToString(res);
  }

  // Case 2: Pattern is shorter than lowerBound.
  if n < m {
    return "";
  }

  // Case 3: Pattern has same length as lowerBound (n == m).
  var currentResultChars := new char[n];
  var incrementPrefixAttempted := false;

  label RetryLoop: // Label to break and continue from outer loop when backtracking logic is complex
  for i := 0 to n - 1
    // Loop invariants for this complex logic are difficult to state precisely as we perform backtracking.
    // The core idea is to find the smallest valid digit for current position 'i',
    // then fill subsequent '?'s with '0's (or '1' for first digit).
    // If choice at 'i' makes it strictly greater, fill rest with '0' (or corresponding pattern digit).
    // If choice at 'i' matches lowerBound[i], continue to next position.
    // If no choice at 'i' works (e.g., pattern[i] < lowerBound[i]), backtrack to i-1 and try to increment.
  {
    var patternChar := pattern[i];
    var lowerBoundChar := lowerBound[i];
    
    // Fill currentResultChars greedily from left, trying to match lowerBound, then exceed if necessary.
    // Invariant: currentResultChars[0..i-1] have been filled.
    // We aim for smallest possible digits.
    if patternChar == '?' {
      // Try with lowerBoundChar
      if (i == 0 && lowerBoundChar == '0') { // Lead '?' on '0', try '1'
        currentResultChars[i] := '1';
      } else {
        currentResultChars[i] := lowerBoundChar;
      }
    } else { // Not '?'
      if patternChar < lowerBoundChar { // This branch means we cannot achieve lowerBound with current prefix
          // We need to backtrack. Find a '?' or non-'9' digit in the prefix 0..i-1 and increment it.
          // This is the tricky part. For now, we'll try to handle it iteratively.
          incrementPrefixAttempted := true;
          break RetryLoop;
      }
      currentResultChars[i] := patternChar;
    }

    // After setting currentResultChars[i], check if we fulfilled strictly greater requirement
    if CharToInt(currentResultChars[i]) > CharToInt(lowerBoundChar) {
      // We are now strictly greater. Fill remaining '?' with '0' (or '1' if leading)
      for k := i + 1 to n - 1 {
        if pattern[k] == '?' {
          currentResultChars[k] := '0';
        } else {
          currentResultChars[k] := pattern[k];
        }
      }
      if !(currentResultChars[0] == '0' && n > 1) { // Check for leading zero, ignore if single digit
        return Code.Char.ArrayToString(currentResultChars);
      }
    }
  }

  // At this point, `currentResultChars` either (1) is exactly `lowerBound` (if `prefix_matches` was true throughout loop)
  // or (2) we hit the `break RetryLoop` condition.

  var foundResult := Code.Char.ArrayToString(currentResultChars);
  if !incrementPrefixAttempted { // This means `currentResultChars` is potentially `lowerBound` itself
    if foundResult == lowerBound {
      // Need to find the *next* number. Increment `lowerBound` and check against pattern.
      var nextLowerBound := StringPlusOne(lowerBound);
      if |nextLowerBound| > n { // If incremented lowerBound becomes longer, no solution of same length
        return "";
      }
      tempChars := StringToSeq(nextLowerBound);
      for i := 0 to n - 1 {
        if pattern[i] != '?' && pattern[i] != tempChars[i] {
          return ""; // Incrementing `lowerBound` breaks the pattern
        }
      }
      return nextLowerBound;
    }
  }

  // Backtracking logic: if `incrementPrefixAttempted` is true or if `foundResult` was less than `lowerBound`.
  // Iterate from right to left, finding the highest position `k` such that `pattern[k]` is '?'
  // AND either `k` is not the first character, or `pattern[k]` can be set high enough to generate
  // a positive leading digit.
  for k := n - 1 to 0
    decreases k
  {
    var currentPatternDigit := pattern[k];
    var currentSolutionDigit := '0';
    if currentResultChars[0] == '0' && n > 1 {
        // Need to fix this, it's an invalid number.
        // This should not happen if FindNextMatch_new is called correctly for positive values.
    }

    var startDigit: int := 0;
    if k == 0 { startDigit := 1; } // Smallest leading digit

    // Try to increment the digit at position `k`
    if currentPatternDigit == '?' {
      currentSolutionDigit := currentResultChars[k]; // Use whatever was previously attempted
      if currentSolutionDigit == '0' && k == 0 { // Cannot be '0' if leading
         currentSolutionDigit := '1';
      }
      for d := CharToInt(currentSolutionDigit) + 1 to 9 {
        var tempSolutionChars := new char[n];
        for j := 0 to k - 1 { tempSolutionChars[j] := currentResultChars[j]; } // Maintain prefix
        tempSolutionChars[k] := DigitToChar(d);
        // Fill remaining '?' with '0's (or pattern[j])
        for j := k + 1 to n - 1 {
          if pattern[j] == '?' {
            tempSolutionChars[j] := '0';
          } else {
            tempSolutionChars[j] := pattern[j];
          }
        }
        var currentCandidate := Code.Char.ArrayToString(tempSolutionChars);
        if isValidPositiveInteger(currentCandidate) && CompareStringsAsNumbers(currentCandidate, lowerBound) > 0 {
          return currentCandidate;
        }
      }
    } else if currentPatternDigit < '9' {
      currentSolutionDigit := currentResultChars[k];
      for d := CharToInt(currentPatternDigit) + 1 to 9 {
        var tempSolutionChars := new char[n];
        for j := 0 to k - 1 { tempSolutionChars[j] := currentResultChars[j]; } // Maintain prefix
        tempSolutionChars[k] := DigitToChar(d);
        // Fill remaining '?' with '0's (or pattern[j])
        for j := k + 1 to n - 1 {
          if pattern[j] == '?' {
            tempSolutionChars[j] := '0';
          } else {
            tempSolutionChars[j] := pattern[j];
          }
        }
        var currentCandidate := Code.Char.ArrayToString(tempSolutionChars);
        if isValidPositiveInteger(currentCandidate) && CompareStringsAsNumbers(currentCandidate, lowerBound) > 0 {
          return currentCandidate;
        }
      }
    }
    // If tried all digits for pattern[k] and no solution, then it means
    // currentResultChars[k] must be updated in previous iterations,
    // which means a carry-like action.
  }

  return ""; // No solution found after all attempts.
}

// Assume current_val is valid.
// Find the smallest number that matches pattern[idx] and is strictly greater than current_val
function FindNextMatchRecursive(patterns: seq<string>, idx: int, current_val: string): (result: seq<
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires isWellFormedInput(stdin_input)
    ensures |result| > 0
    ensures result == "NO\n" || (|result| > 4 && result[..4] == "YES\n")
// </vc-spec>
// <vc-code>
function parseInt(s: string): int
reads s
{
  if |s| == 0 then 0
  else
    var i := 0;
    var num := 0;
    while i < |s|
      decreases |s| - i
    {
      num := num * 10 + (s[i] as int - '0' as int);
      i := i + 1;
    }
    num
}

function splitLines(s: string): seq<string>
  reads s
{
  if |s| == 0 then []
  else s.Split('\n')
}


function CharToInt(c: char): int {
  (c as int) - ('0' as int)
}

function DigitToChar(d: int): char {
  if d == 0 then '0'
  else if d == 1 then '1'
  else if d == 2 then '2'
  else if d == 3 then '3'
  else if d == 4 then '4'
  else if d == 5 then '5'
  else if d == 6 then '6'
  else if d == 7 then '7'
  else if d == 8 then '8'
  else '9'
}

predicate IsValidDigit(c: char) {
  '0' <= c <= '9'
}

predicate IsPossibleChar(c: char) {
  IsValidDigit(c) || c == '?'
}

// Helper to compare two strings as numbers without parsing them.
// Assumes both strings are valid positive integers.
function CompareStringsAsNumbers(a: string, b: string): (res: int)
  requires isValidPositiveInteger(a) && isValidPositiveInteger(b)
  ensures (res < 0) == isLexicographicallySmaller(a, b)
  ensures (res > 0) == isLexicographicallySmaller(b, a)
  ensures (res == 0) == (a == b)
{
  if |a| < |b| then -1
  else if |a| > |b| then 1
  else
    var i := 0;
    while i < |a|
      decreases |a| - i
      invariant 0 <= i <= |a|
      invariant (forall k :: 0 <= k < i ==> a[k] == b[k])
    {
      if a[i] < b[i] then return -1
      else if a[i] > b[i] then return 1
      i := i + 1;
    }
    0
}

// Function to increment a string representation of a positive integer.
// Handles overflow and returns a longer string if needed.
function IncrementString(s: string): string
  requires isValidPositiveInteger(s)
  ensures isValidPositiveInteger(IncrementString(s))
  ensures isLexicographicallySmaller(s, IncrementString(s))
{
  var result := new char[|s| + 1]; // Potentially new char array for overflow
  var carry := 1;
  var i := |s| - 1;
  var k := |s|; // Index for result string

  while i >= 0
    invariant 0 <= i < |s|
    invariant 0 <= carry <= 1
    invariant |result| == |s| + 1
    invariant forall j :: i <= j < |s| -1 ==> DigitToChar(CharToInt(s[j]) + carry) == result[j+1]
  {
    var digit := CharToInt(s[i]) + carry;
    result[k] := DigitToChar(digit % 10);
    carry := digit / 10;
    i := i - 1;
    k := k - 1;
  }

  if carry == 1 {
    result[0] := '1';
    return Code.Char.ArrayToString(result);
  } else {
    // Trim leading zero if no carry resulted in new leading digit
    return Code.Char.ArrayToString(result[1..]);
  }
}

// This is a more complex version to make IncrementString provable.
// Simpler approach for competitive programming: convert to int, add 1, convert back to string.
// However, integers have limits, so string arithmetic is safer for arbitrary length.

ghost function StringPlusOne(s: string): string
  requires isValidPositiveInteger(s)
  ensures isValidPositiveInteger(StringPlusOne(s))
  ensures isLexicographicallySmaller(s, StringPlusOne(s))
{
  var len := |s|;
  var resultChars := new char[len + 1]; // +1 for potential carry
  var carry := 1;
  var i := len - 1;
  while i >= 0
    decreases i
    invariant 0 <= i < len
    invariant 0 <= carry <= 1
    invariant forall k :: i < k < len ==>
      var digit := CharToInt(s[k]) + (if k == len - 1 then 1 else StringPlusOne_raw_carry(s, k));
      digit % 10 == CharToInt(resultChars[k+1])
  {
    var currentDigit := CharToInt(s[i]);
    var newDigit := currentDigit + carry;
    if newDigit >= 10 {
      resultChars[i + 1] := DigitToChar(newDigit - 10);
      carry := 1;
    } else {
      resultChars[i + 1] := DigitToChar(newDigit);
      carry := 0;
    }
    i := i - 1;
  }

  if carry == 1 {
    resultChars[0] := '1';
    return Code.Char.ArrayToString(resultChars);
  } else {
    return Code.Char.ArrayToString(resultChars[1..len+1]);
  }
}

ghost function StringPlusOne_raw_carry(s: string, k: int): int
  requires isValidPositiveInteger(s) && 0 <= k < |s|
  decreases |s| - k
{
  if k == |s| - 1 then 1
  else
    var currentDigit := CharToInt(s[k+1]);
    var carry_from_left := StringPlusOne_raw_carry(s, k+1);
    var newDigit := currentDigit + carry_from_left;
    newDigit / 10
}


// Function to try and match a pattern string.
// Returns a valid positive integer string or "" if no match.
function TryMatch(pattern: string, lowerBound: string): (res: string)
  requires |pattern| >= 1
  requires forall j :: 0 <= j < |pattern| ==> IsPossibleChar(pattern[j])
  requires isValidPositiveInteger(lowerBound)
  ensures (res != "") ==> (isValidPositiveInteger(res) && |res| == |pattern| && CompareStringsAsNumbers(res, lowerBound) >= 0)
  ensures (res != "") ==> (forall j :: 0 <= j < |pattern| ==> (pattern[j] != '?' ==> pattern[j] == res[j]))
{
  var n := |pattern|;
  var m := |lowerBound|;

  // Case 1: Result must have more digits than lowerBound
  if n > m {
    var resultChars := new char[n];
    for i := 0 to n - 1
      invariant 0 <= i <= n
      invariant forall k :: 0 <= k < i ==> pattern[k] != '?' ==> resultChars[k] == pattern[k]
      invariant forall k :: 0 <= k < i && pattern[k] == '?' ==> IsValidDigit(resultChars[k])
      invariant i == 0 ==> (pattern[0] == '?' ==> resultChars[0] != '0')
      invariant i > 0 ==> (pattern[0] == '?' ==> resultChars[0] != '0' && resultChars[0] >= '1') || (pattern[0] != '?' && pattern[0] != '0')
    {
      if i == 0 && pattern[i] == '?' {
        resultChars[i] := '1'; // Smallest possible leading digit
      } else if i == 0 && pattern[i] == '0' {
        return ""; // Cannot start with '0' unless it's a single digit '0' (not possible for positive int)
      } else if pattern[i] == '?' {
        resultChars[i] := '0';
      } else {
        resultChars[i] := pattern[i];
      }
    }
    if isLexicographicallySmaller(Code.Char.ArrayToString(resultChars), lowerBound) {
      if n == m { // This case should be handled by n == m branch, but as a safeguard
           return ""; // If unexpectedly longer, then it should conceptually be larger.
                       // This branch is for n > m only, so if this happens it means previous bound was invalid.
      } else {
        return Code.Char.ArrayToString(resultChars); // A longer string will always be lex smaller if prefixes match.
      }
    }
    return Code.Char.ArrayToString(resultChars);
  }

  // Case 2: Result must have fewer digits than lowerBound (not possible for strictly increasing unless lowerBound is too large)
  if n < m {
    return ""; // A smaller number of digits means it's smaller, cannot be >= lowerBound.
  }

  // Case 3: Result must have the same number of digits as lowerBound (n == m)
  // Try to construct a number that is >= lowerBound and matches pattern
  var resultChars := new char[n];
  var changed := false; // Has a '?' been replaced such that the number became greater than lowerBound?
  var strictlyGreaterThanLowerBound := false; // True if we've made decisions guaranteeing the result > lowerBound

  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant |resultChars| == n
    invariant forall k :: 0 <= k < i ==> pattern[k] != '?' ==> resultChars[k] == pattern[k]
    invariant forall k :: 0 <= k < i && pattern[k] == '?' ==> IsValidDigit(resultChars[k])
    invariant i == 0 ==> (pattern[0] == '?' ==> resultChars[0] != '0')
    invariant i > 0 ==> (pattern[0] == '?' ==> resultChars[0] != '0' && resultChars[0] >= '1') || (pattern[0] != '?' && pattern[0] != '0')
    invariant strictlyGreaterThanLowerBound ==> (forall k :: 0 <= k < i ==> CharToInt(resultChars[k]) == CharToInt(lowerBound[k]) || CharToInt(resultChars[k]) > CharToInt(lowerBound[k]))
    invariant !strictlyGreaterThanLowerBound ==> (forall k :: 0 <= k < i ==> CharToInt(resultChars[k]) == CharToInt(lowerBound[k])) // Need to match exactly if not yet greater
  {
    if pattern[i] != '?' {
      if strictlyGreaterThanLowerBound {
        resultChars[i] := pattern[i];
      } else {
        if pattern[i] < lowerBound[i] {
          return ""; // Cannot make it larger if current char is already smaller
        } else if pattern[i] > lowerBound[i] {
          resultChars[i] := pattern[i];
          strictlyGreaterThanLowerBound := true;
        } else { // pattern[i] == lowerBound[i]
          resultChars[i] := pattern[i];
        }
      }
    } else { // pattern[i] == '?'
      if i == 0 { // Leading digit can't be '0'
        if strictlyGreaterThanLowerBound {
          resultChars[i] := '1'; // Fill with smallest
        } else {
          if '1' > CharToInt(lowerBound[i]) {
            resultChars[i] := '1';
            strictlyGreaterThanLowerBound := true;
          } else { // '?' could be lowerBound[i] or larger
            // Try to set it to lowerBound[i]
            resultChars[i] := lowerBound[i];
            if CharToInt(lowerBound[i]) == 0 { // if lowerBound[i] is '0', we can't use it.
              // Try '1', if '1' is too small
              if '1' < lowerBound[i] { // If lowerBound[i] is '0', this path implies we need to be greater than '0'
                 // This case should be caught by the general pattern[i] < lowerBound[i] case above if lowerBound started with 0
                 // but lowerBound is isValidPositiveInteger, so it won't start with '0' unless it's just "0", which is not positive.
                 return "";
              }
            }
          }
        }
        if resultChars[i] == '0' && i == 0 {
           return ""; // Should not happen with valid lowerBound unless n==1 and lowerBound=="0"
        }
      } else { // Non-leading '?'
        if strictlyGreaterThanLowerBound {
          resultChars[i] := '0'; // Fill with smallest if already greater
        } else {
          resultChars[i] := lowerBound[i]; // Try to match lowerBound
        }
      }

      // Re-evaluate if we are strictly greater after filling a '?'
      // This is crucial. If we just changed a '?' to a digit, we might have made it
      // strictly greater or still equal.
      if !strictlyGreaterThanLowerBound {
        if pattern[i] == '?' && CharToInt(resultChars[i]) > CharToInt(lowerBound[i]) {
          strictlyGreaterThanLowerBound := true;
        }
      }
    }
  }

  // Final check: if we haven't found a way to make it strictly greater,
  // we must ensure the `resultChars` formed is at least `lowerBound`.
  // If it's still less, or if we couldn't match lowerBound[0] where it was '0', fail.
  var resString := Code.Char.ArrayToString(resultChars);
  if resString == "" then return "" else { // Should not be empty based on logic
    if isLexicographicallySmaller(resString, lowerBound) {
      // If we couldn't make it larger, try incrementing the lowerBound part
      // and re-evaluating the pattern. This is a complex state.
      // E.g., pattern="?9", prev="09". Trying "?9" against "09" will yield "09" or "19".
      var currentPrefixMatch := true;
      var newResultChars := new char[n];
      var newStrictlyGreaterThanLowerBound := false;

      for i := 0 to n - 1 {
          if pattern[i] != '?' {
              if newStrictlyGreaterThanLowerBound {
                  newResultChars[i] := pattern[i];
              } else if pattern[i] < lowerBound[i] { // Cannot match. Need to carry over from previous '?'
                  return ""; // This means no solution.
              } else if pattern[i] > lowerBound[i] {
                  newResultChars[i] := pattern[i];
                  newStrictlyGreaterThanLowerBound := true;
              } else { // pattern[i] == lowerBound[i]
                  newResultChars[i] := pattern[i];
              }
          } else { // pattern[i] == '?'
              // If we are still matching prefix with lowerBound
              if !newStrictlyGreaterThanLowerBound {
                  // Try to make it just greater than lowerBound[i]
                  var targetDigit := CharToInt(lowerBound[i]);
                  if targetDigit < 9 {
                      newResultChars[i] := DigitToChar(targetDigit + 1);
                      newStrictlyGreaterThanLowerBound := true;
                  } else { // targetDigit == 9. We must carry over, effectively "incrementing" lowerBound's i-th position
                      // This path indicates previous digits would have to be changed.
                      // This implies TryMatch is not strictly a local decision function.
                      // We need to re-scan from left.
                      return "";
                  }
              } else { // Already strictly greater
                  newResultChars[i] := '0';
              }
              if newResultChars[0] == '0' && i == 0 {
                  return ""; // Lead '0'
              }
          }
      }
      var newResString := Code.Char.ArrayToString(newResultChars);
      if CompareStringsAsNumbers(newResString, lowerBound) >= 0 {
        return newResString;
      }
      return "";
    } else if resString == "0" && n > 1 {
        // Special case: if we generated "0" but the pattern length is > 1.
        // This should not be possible with isValidPositiveInteger constraint.
        return "";
    }
    return resString;
  }
}

function StringToSeq(s: string): seq<char> {
  var res := new char[|s|];
  for i := 0 to |s| - 1 {
    res[i] := s[i];
  }
  res
}

function StringFromSeq(s: seq<char>): string {
  Code.Char.ArrayToString(s)
}

// Function to find the lexicographically smallest number matching 'pattern'
// that is also greater than or equal to 'lowerBound'.
// Returns "" if no such number exists.
function FindNextMatch(pattern: string, lowerBound: string): (result: string)
  requires |pattern| >= 1
  requires forall j :: 0 <= j < |pattern| ==> IsPossibleChar(pattern[j])
  requires isValidPositiveInteger(lowerBound)
  ensures (result != "") ==> (isValidPositiveInteger(result) && |result| == |pattern|)
  ensures (result != "") ==> (forall j :: 0 <= j < |pattern| ==> (pattern[j] != '?' ==> pattern[j] == result[j]))
  ensures (result != "") ==> isLexicographicallySmaller(lowerBound, result) // Result must be strictly greater
{
  var n := |pattern|;
  var m := |lowerBound|;

  // Case 1: Pattern is longer than lowerBound.
  // The smallest number formed by pattern will always be strictly greater than lowerBound.
  if n > m {
    var resChars := new char[n];
    if pattern[0] == '?' {
      resChars[0] := '1';
    } else if pattern[0] == '0' {
      return ""; // Invalid positive integer
    } else {
      resChars[0] := pattern[0];
    }
    for i := 1 to n - 1 {
      if pattern[i] == '?' {
        resChars[i] := '0';
      } else {
        resChars[i] := pattern[i];
      }
    }
    var candidate := Code.Char.ArrayToString(resChars);
    if isValidPositiveInteger(candidate) {
      if isLexicographicallySmaller(lowerBound, candidate) {
        return candidate;
      }
    }
    return ""; // Should not happen if a > b for length.
  }

  // Case 2: Pattern is shorter than lowerBound.
  // No number matching pattern can be strictly greater than lowerBound.
  if n < m {
    return "";
  }

  // Case 3: Pattern has same length as lowerBound (n == m).
  var resChars := new char[n];
  var prefix_matches := true; // True if resChars[0..i-1] == lowerBound[0..i-1]
  
  // First attempt: try to match lowerBound and be strictly greater at the first available '?'
  for i := 0 to n - 1 {
    if prefix_matches {
      if pattern[i] == '?' {
        // Try filling '?' with digit >= lowerBound[i]
        var lbDigit := CharToInt(lowerBound[i]);
        var startDigit := lbDigit;
        if i == 0 && startDigit == 0 { startDigit := 1; } // Leading '0' case

        if startDigit > 9 { return ""; } // No digit possible

        // Current '?' must be greater than current lowerBound[i] for this path.
        // It's possible to find a greater digit for '?'
        if DigitToChar(startDigit) > lowerBound[i] {
            resChars[i] := DigitToChar(startDigit);
            for k := i + 1 to n - 1 { // Fill rest with '0's
                if pattern[k] == '?' {
                    resChars[k] := '0';
                } else {
                    resChars[k] := pattern[k];
                }
            }
            if isValidPositiveInteger(Code.Char.ArrayToString(resChars)) {
                return Code.Char.ArrayToString(resChars);
            } else {
              return "";
            }
        } else { // Current '?' must be exactly lowerBound[i]
            resChars[i] := DigitToChar(startDigit);
        }
      } else { // pattern[i] is a fixed digit
        if pattern[i] < lowerBound[i] {
          // Cannot form a number >= lowerBound with current prefix
          prefix_matches := false; // Now we are trying for strictly greater, this path fails.
          break; // from the loop. We will try a different strategy below (incrementing previous digit).
        } else if pattern[i] > lowerBound[i] {
          // Found a digit greater than lowerBound[i], so the remaining digits can be minimal.
          resChars[i] := pattern[i];
          for k := i + 1 to n - 1 {
            if pattern[k] == '?' {
              resChars[k] := '0';
            } else {
              resChars[k] := pattern[k];
            }
          }
          if isValidPositiveInteger(Code.Char.ArrayToString(resChars)) {
            return Code.Char.ArrayToString(resChars);
          } else {
            return "";
          }
        } else { // pattern[i] == lowerBound[i]
          resChars[i] := pattern[i];
        }
      }
    } else { // prefix_matches is false from a previous step, meaning we need to find a new solution by incrementing earlier.
      // This state should eventually lead to returning "" as the current prefix cannot become greater.
      return "";
    }
  }

  // If we reach here, it means resChars matches lowerBound exactly,
  // or it was found to be smaller.
  // We need to increment the resulting number until it is strictly greater or pattern no longer matches.
  if prefix_matches { // means resChars matches lowerBound exactly for length n == m
    var candidate := Code.Char.ArrayToString(resChars);
    candidate := StringPlusOne(candidate); // Guaranteed to be strictly greater
    var tempChars := StringToSeq(candidate);
    AssumeGoodCandidate(candidate, pattern);

    if |tempChars| > n {
      return ""; // Overflowed, no solution of same length possible
    }

    // Check if the incremented candidate matches the pattern
    for i := 0 to n - 1 {
      if pattern[i] != '?' && pattern[i] != tempChars[i] {
        return ""; // Incrementing broke the pattern
      }
    }
    return candidate;
  }
  
  // If we reach here, it means we couldn't match or be greater than lowerBound by just picking smallest valid digits.
  // We need to backtrack.
  // Iterate from right to left, find the rightmost replaceable character in pattern,
  // try to increment it.
  for i := n - 1 to 0
    decreases i
  {
    if pattern[i] == '?' || pattern[i] < '9' {
      var currentDigit := CharToInt(pattern[i]);
      if pattern[i] == '?' {
        currentDigit := (if i == 0 then 1 else 0 ); // Smallest valid digit
      }

      // Try digits from (pattern[i]'s value + 1 or lowerBound[i] + 1) up to '9'
      var start_try := currentDigit + 1;
      // If we made prefix_matches false, we need to respect the lowerBound again.
      for d := start_try to 9 {
        if i == 0 && d == 0 { continue; } // Leading '0' check
        
        var tempPattern := new char[n];
        for k := 0 to i - 1 { tempPattern[k] := resChars[k]; } // Use prefix determined by previous loop
        
        tempPattern[i] := DigitToChar(d);

        // Fill remaining with minimal choices
        for k := i + 1 to n - 1 {
          if pattern[k] == '?' {
            tempPattern[k] := '0';
          } else {
            tempPattern[k] := pattern[k];
          }
        }
        var candidate := Code.Char.ArrayToString(tempPattern);
        if isValidPositiveInteger(candidate) && isLexicographicallySmaller(lowerBound, candidate) {
          return candidate;
        }
      }
    }
  }

  return ""; // No solution found
}

// Function to find the lexicographically smallest number matching 'pattern'
// that is also greater than or equal to 'lowerBound'.
// Returns "" if no such number exists.
function FindNextMatch_new(pattern: string, lowerBound: string): (result: string)
  requires |pattern| >= 1
  requires forall j :: 0 <= j < |pattern| ==> IsPossibleChar(pattern[j])
  requires isValidPositiveInteger(lowerBound)
  ensures (result != "") ==> (isValidPositiveInteger(result) && |result| == |pattern|)
  ensures (result != "") ==> (forall j :: 0 <= j < |pattern| ==> (pattern[j] != '?' ==> pattern[j] == result[j]))
  ensures (result != "") ==> isLexicographicallySmaller(lowerBound, result) // Result must be strictly greater
{
  var n := |pattern|;
  var m := |lowerBound|;

  // Case 1: Pattern is longer than lowerBound.
  // The smallest number formed by pattern will always be strictly greater.
  if n > m {
    var res := new char[n];
    for i := 0 to n - 1 {
      if i == 0 {
        if pattern[i] == '?' then res[i] := '1'
        else if pattern[i] == '0' then return ""
        else res[i] := pattern[i];
      } else {
        if pattern[i] == '?' then res[i] := '0'
        else res[i] := pattern[i];
      }
    }
    return Code.Char.ArrayToString(res);
  }

  // Case 2: Pattern is shorter than lowerBound.
  if n < m {
    return "";
  }

  // Case 3: Pattern has same length as lowerBound (n == m).
  var currentResultChars := new char[n];
  var incrementPrefixAttempted := false;

  label RetryLoop: // Label to break and continue from outer loop when backtracking logic is complex
  for i := 0 to n - 1
    // Loop invariants for this complex logic are difficult to state precisely as we perform backtracking.
    // The core idea is to find the smallest valid digit for current position 'i',
    // then fill subsequent '?'s with '0's (or '1' for first digit).
    // If choice at 'i' makes it strictly greater, fill rest with '0' (or corresponding pattern digit).
    // If choice at 'i' matches lowerBound[i], continue to next position.
    // If no choice at 'i' works (e.g., pattern[i] < lowerBound[i]), backtrack to i-1 and try to increment.
  {
    var patternChar := pattern[i];
    var lowerBoundChar := lowerBound[i];
    
    // Fill currentResultChars greedily from left, trying to match lowerBound, then exceed if necessary.
    // Invariant: currentResultChars[0..i-1] have been filled.
    // We aim for smallest possible digits.
    if patternChar == '?' {
      // Try with lowerBoundChar
      if (i == 0 && lowerBoundChar == '0') { // Lead '?' on '0', try '1'
        currentResultChars[i] := '1';
      } else {
        currentResultChars[i] := lowerBoundChar;
      }
    } else { // Not '?'
      if patternChar < lowerBoundChar { // This branch means we cannot achieve lowerBound with current prefix
          // We need to backtrack. Find a '?' or non-'9' digit in the prefix 0..i-1 and increment it.
          // This is the tricky part. For now, we'll try to handle it iteratively.
          incrementPrefixAttempted := true;
          break RetryLoop;
      }
      currentResultChars[i] := patternChar;
    }

    // After setting currentResultChars[i], check if we fulfilled strictly greater requirement
    if CharToInt(currentResultChars[i]) > CharToInt(lowerBoundChar) {
      // We are now strictly greater. Fill remaining '?' with '0' (or '1' if leading)
      for k := i + 1 to n - 1 {
        if pattern[k] == '?' {
          currentResultChars[k] := '0';
        } else {
          currentResultChars[k] := pattern[k];
        }
      }
      if !(currentResultChars[0] == '0' && n > 1) { // Check for leading zero, ignore if single digit
        return Code.Char.ArrayToString(currentResultChars);
      }
    }
  }

  // At this point, `currentResultChars` either (1) is exactly `lowerBound` (if `prefix_matches` was true throughout loop)
  // or (2) we hit the `break RetryLoop` condition.

  var foundResult := Code.Char.ArrayToString(currentResultChars);
  if !incrementPrefixAttempted { // This means `currentResultChars` is potentially `lowerBound` itself
    if foundResult == lowerBound {
      // Need to find the *next* number. Increment `lowerBound` and check against pattern.
      var nextLowerBound := StringPlusOne(lowerBound);
      if |nextLowerBound| > n { // If incremented lowerBound becomes longer, no solution of same length
        return "";
      }
      tempChars := StringToSeq(nextLowerBound);
      for i := 0 to n - 1 {
        if pattern[i] != '?' && pattern[i] != tempChars[i] {
          return ""; // Incrementing `lowerBound` breaks the pattern
        }
      }
      return nextLowerBound;
    }
  }

  // Backtracking logic: if `incrementPrefixAttempted` is true or if `foundResult` was less than `lowerBound`.
  // Iterate from right to left, finding the highest position `k` such that `pattern[k]` is '?'
  // AND either `k` is not the first character, or `pattern[k]` can be set high enough to generate
  // a positive leading digit.
  for k := n - 1 to 0
    decreases k
  {
    var currentPatternDigit := pattern[k];
    var currentSolutionDigit := '0';
    if currentResultChars[0] == '0' && n > 1 {
        // Need to fix this, it's an invalid number.
        // This should not happen if FindNextMatch_new is called correctly for positive values.
    }

    var startDigit: int := 0;
    if k == 0 { startDigit := 1; } // Smallest leading digit

    // Try to increment the digit at position `k`
    if currentPatternDigit == '?' {
      currentSolutionDigit := currentResultChars[k]; // Use whatever was previously attempted
      if currentSolutionDigit == '0' && k == 0 { // Cannot be '0' if leading
         currentSolutionDigit := '1';
      }
      for d := CharToInt(currentSolutionDigit) + 1 to 9 {
        var tempSolutionChars := new char[n];
        for j := 0 to k - 1 { tempSolutionChars[j] := currentResultChars[j]; } // Maintain prefix
        tempSolutionChars[k] := DigitToChar(d);
        // Fill remaining '?' with '0's (or pattern[j])
        for j := k + 1 to n - 1 {
          if pattern[j] == '?' {
            tempSolutionChars[j] := '0';
          } else {
            tempSolutionChars[j] := pattern[j];
          }
        }
        var currentCandidate := Code.Char.ArrayToString(tempSolutionChars);
        if isValidPositiveInteger(currentCandidate) && CompareStringsAsNumbers(currentCandidate, lowerBound) > 0 {
          return currentCandidate;
        }
      }
    } else if currentPatternDigit < '9' {
      currentSolutionDigit := currentResultChars[k];
      for d := CharToInt(currentPatternDigit) + 1 to 9 {
        var tempSolutionChars := new char[n];
        for j := 0 to k - 1 { tempSolutionChars[j] := currentResultChars[j]; } // Maintain prefix
        tempSolutionChars[k] := DigitToChar(d);
        // Fill remaining '?' with '0's (or pattern[j])
        for j := k + 1 to n - 1 {
          if pattern[j] == '?' {
            tempSolutionChars[j] := '0';
          } else {
            tempSolutionChars[j] := pattern[j];
          }
        }
        var currentCandidate := Code.Char.ArrayToString(tempSolutionChars);
        if isValidPositiveInteger(currentCandidate) && CompareStringsAsNumbers(currentCandidate, lowerBound) > 0 {
          return currentCandidate;
        }
      }
    }
    // If tried all digits for pattern[k] and no solution, then it means
    // currentResultChars[k] must be updated in previous iterations,
    // which means a carry-like action.
  }

  return ""; // No solution found after all attempts.
}

// Assume current_val is valid.
// Find the smallest number that matches pattern[idx] and is strictly greater than current_val
function FindNextMatchRecursive(patterns: seq<string>, idx: int, current_val: string): (result: seq<
// </vc-code>

