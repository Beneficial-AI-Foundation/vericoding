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
function Pow10(k: nat): nat
  ensures Pow10(k) > 0
{
  if k == 0 then 1 else 10 * Pow10(k - 1)
}

function stringToNat(s: string): nat
  requires isValidPositiveInteger(s)
  ensures s != "0" ==> stringToNat(s) > 0
  ensures s == "0" ==> stringToNat(s) == 0
  decreases |s|
{
  if |s| == 0 then 0
  else if |s| == 1 then (s[0] - '0') as nat
  else
    var lastDigit := (s[|s|-1] - '0') as nat;
    var prefix := s[0 .. |s|-1];
    stringToNat(prefix) * 10 + lastDigit
}

lemma lemma_stringToNat_monotonic(s1: string, s2: string)
  requires isValidPositiveInteger(s1)
  requires isValidPositiveInteger(s2)
  requires |s1| == |s2|
  requires s1 < s2
  ensures stringToNat(s1) < stringToNat(s2)
{
  if |s1| == 0 {
    // Vacuously true
  } else if |s1| == 1 {
    assert (s1[0] - '0') < (s2[0] - '0');
  } else {
    var s1_prefix := s1[0 .. |s1|-1];
    var s2_prefix := s2[0 .. |s2|-1];
    if s1_prefix < s2_prefix {
      lemma_stringToNat_monotonic(s1_prefix, s2_prefix);
      assert stringToNat(s1_prefix) < stringToNat(s2_prefix);
      assert stringToNat(s1) < stringToNat(s2);
    } else {
      assert s1_prefix == s2_prefix; // Since |s1|=|s2| and s1[0..|s1|-1] is not < s2[0..|s2|-1], it must be equal since s1 < s2
      assert s1[|s1|-1] < s2[|s2|-1];
      assert (s1[|s1|-1] - '0') < (s2[|s2|-1] - '0');
      assert stringToNat(s1) < stringToNat(s2);
    }
  }
}

lemma lemma_isLexicographicallySmaller_transitive(a: string, b: string, c: string)
  requires isValidPositiveInteger(a) && isValidPositiveInteger(b) && isValidPositiveInteger(c)
  requires isLexicographicallySmaller(a, b)
  requires isLexicographicallySmaller(b, c)
  ensures isLexicographicallySmaller(a, c)
{
  if |a| < |b| {
    if |b| < |c| {
      assert |a| < |c|;
    } else if |b| == |c| && b < c {
      assert |a| < |c|;
    }
  } else if |a| == |b| && a < b {
    if |b| < |c| {
      assert |a| < |c|;
    } else if |b| == |c| && b < c {
      lemma_stringToNat_monotonic(a, b);
      lemma_stringToNat_monotonic(b, c);
      assert stringToNat(a) < stringToNat(b);
      assert stringToNat(b) < stringToNat(c);
      assert stringToNat(a) < stringToNat(c);
      // To prove a < c for equal length:
      // If s1 < s2 and s2 < s3 and |s1|=|s2|=|s3|, then s1 < s3
      // This is a property of string comparison
      assert a < c;
    }
  }
}

lemma lemma_isStrictlyIncreasingSequence_subset(nums: seq<string>, i: int, k: int)
  requires 0 <= i <= k < |nums|
  requires forall j :: 0 <= j < |nums| ==> isValidPositiveInteger(nums[j])
  requires isStrictlyIncreasingSequence(nums)
  ensures isLexicographicallySmaller(nums[i], nums[k])
  decreases k - i
{
  if i == k {
    // vacuous
  } else if i + 1 == k {
    assert isLexicographicallySmaller(nums[i], nums[i+1]);
  } else {
    lemma_isStrictlyIncreasingSequence_subset(nums, i, k-1);
    lemma_isLexicographicallySmaller_transitive(nums[i], nums[k-1], nums[k]);
  }
}


function createSolution(
  inputStrings: seq<string>,
  idx: int,
  currentSolution: seq<string>,
  prevFound: string
): (seq<string>, bool)
  requires 0 <= idx <= |inputStrings|
  requires idx == 0 ==> currentSolution == []
  requires idx > 0 ==> currentSolution != [] && |currentSolution| == idx && isValidPositiveInteger(prevFound)
  requires (idx > 0 && idx < |inputStrings|) ==> isValidPositiveInteger(currentSolution[idx-1]) // Ensure the last element added is valid
  // requires (idx == 0) || (idx > 0 && isValidPositiveInteger(prevFound))
  // requires |currentSolution| == idx
  // ensures (idx == |inputStrings| && !success) ==> currentSolution == [] // If we explore all paths and fail, return empty.
  ensures |currentSolution| == |inputStrings| && success ==> isValidSequenceSolution(inputStrings, currentSolution)
  decreases |inputStrings| - idx
{
  if idx == |inputStrings| {
    return currentSolution, true;
  }

  var inputString := inputStrings[idx];
  var len := |inputString>;

  // Lemma for stringToNat for all possible values based on inputString
  // This is a common pattern for "guessing" numbers with wildcards

  var minValInt: nat := 0;
  var maxValInt: nat := 0;
  if prevFound != "" {
    minValInt := stringToNat(prevFound) + 1;
  }

  // Calculate min and max possible values based on string length
  var currentMinValByLength: nat;
  var currentMaxValByLength: nat;
  if len == 1 {
    currentMinValByLength := 0;
    currentMaxValByLength := 9;
  } else {
    currentMinValByLength := Pow10(len - 1);
    currentMaxValByLength := Pow10(len) - 1;
  }

  minValInt := max(minValInt, currentMinValByLength);
  maxValInt := min(maxValInt, currentMaxValByLength);


  // Iterate through possible values, convert to string, check validity and recurse
  for k := minValInt to maxValInt {
    var candidateString := k as string;
    if isValidPositiveInteger(candidateString) && |candidateString| == len {
      var match := true;
      for charIdx := 0 to len-1 {
        if inputString[charIdx] != '?' && inputString[charIdx] != candidateString[charIdx] {
          match := false;
          break;
        }
      }
      if match {
        // Here we need to assert that the candidate solution works at this step
        if idx > 0 {
          lemma_stringToNat_monotonic(prevFound, candidateString);
          assert stringToNat(prevFound) < stringToNat(candidateString);
          assert isLexicographicallySmaller(prevFound, candidateString);
        }

        var (restOfSolution, success) := createSolution(
          inputStrings,
          idx + 1,
          currentSolution + [candidateString],
          candidateString
        );

        if success {
          assert isValidSequenceSolution(inputStrings, currentSolution + [candidateString] + restOfSolution[idx+1..]);
          return restOfSolution, true; // Found a solution
        }
      }
    }
  }

  return [], false; // No solution found
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires isWellFormedInput(stdin_input)
    ensures |result| > 0
    ensures result == "NO\n" || (|result| > 4 && result[..4] == "YES\n")
// </vc-spec>
// <vc-code>
{
  var lines := splitLines(stdin_input);
  var n := parseInt(lines[0]);

  if n == 0 {
    return "YES\n";
  }

  var inputStrings := lines[1..n+1];

  var (solution, found) := createSolution(inputStrings, 0, [], "");

  if found {
    return "YES\n" + solution.Join("\n") + "\n";
  } else {
    return "NO\n";
  }
}
// </vc-code>

