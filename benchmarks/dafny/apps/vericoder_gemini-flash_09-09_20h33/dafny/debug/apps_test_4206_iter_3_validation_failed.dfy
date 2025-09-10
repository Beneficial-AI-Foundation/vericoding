predicate ValidInput(input: string)
{
    |input| > 0 &&
    input[|input|-1] == '\n' &&
    |input| >= 2 &&
    (forall i :: 0 <= i < |input|-1 ==> '0' <= input[i] <= '9') &&
    (input[0] != '0' || |input| == 2)
}

function MaxDivisibleBy3Segments(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures MaxDivisibleBy3Segments(s) >= 0
    ensures MaxDivisibleBy3Segments(s) <= |s|
{
    MaxDivisibleBy3SegmentsHelper(s, 0, "", 0)
}

// <vc-helpers>
function MaxDivisibleBy3SegmentsHelper(s: string, index: int, currentSumStr: string, count: int): int
  requires 0 <= index <= |s|
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  requires currentSumStr == "" || (currentSumStr != "" && (currentSumStr as int) >= 0)
  ensures MaxDivisibleBy3SegmentsHelper(s, index, currentSumStr, count) >= count
{
  if index == |s| then
    if currentSumStr != "" && (currentSumStr as int) % 3 == 0 then
      count + 1
    else
      count
  else if currentSumStr != "" && (currentSumStr as int) % 3 == 0 then
    // Option 1: Start a new segment with the current character s[index], and include the current segment
    var include_val := MaxDivisibleBy3SegmentsHelper(s, index + 1, "" + s[index], count + 1);
    // Option 2: Start a new segment with the current character s[index], but DO NOT include the current segment
    // This case should not be considered, as we want to maximize the count
    // Option 3: Exclude the current character s[index] from the current segment and keep looking for a segment
    // No, this is incorrect. We are either extending the current segment or starting a new one.
    // The previous segment is already evaluated. We are at a new index.
    // This part of the logic needs to be about starting a new segment vs extending the current.
    // However, if the currentSumStr % 3 == 0, then we have definitively found a valid segment.
    // So we need to consider starting a new segment from s[index] and adding 1 to count,
    // OR just starting a new segment from s[index] and not adding 1 to count for the current one
    // (meaning the current one was not divisible by 3).
    // The current logic handles the case where currentSumStr is divisible by 3.
    // In that case, we definitely want to take count + 1 and reset current sum.
    // and then compare it with the case where we just skip currentSumStr and start with s[index].
    var exclude_this_segment_include_next := MaxDivisibleBy3SegmentsHelper(s, index + 1, "" + s[index], count);
    
    // So if currentSumStr % 3 == 0:
    // 1. Take count+1, and reset currentSumStr to s[index] (start new segment for next step)
    // 2. Don't take count+1, and reset currentSumStr to s[index] (start new segment for next step - effectively ignoring the just-finished segment)
    // This logic is flawed. The `MaxDivisibleBy3SegmentsHelper` already captures the "best" path from `index`.
    // It should be:
    // a) Extend the current segment: `MaxDivisibleBy3SegmentsHelper(s, index + 1, currentSumStr + s[index], count)`
    // b) Start a new segment: `MaxDivisibleBy3SegmentsHelper(s, index + 1, "" + s[index], count + 1)` (if currentSumStr is divisible by 3)
    // c) Start a new segment without current count: `MaxDivisibleBy3SegmentsHelper(s, index + 1, "" + s[index], count)` (if currentSumStr is not divisible by 3)

    // Let's refine the logic for the `else` block (when `index < |s|`):
    // Two main choices at each `index`:
    // 1. Extend the `currentSumStr` with `s[index]`.
    // 2. Start a new segment with `s[index]`.

    // If `currentSumStr` is divisible by 3:
    // Option A: Take `currentSumStr` as a complete segment (add 1 to `count`), and start a new segment with `s[index]`.
    var optionA := MaxDivisibleBy3SegmentsHelper(s, index + 1, "" + s[index], count + 1);
    // Option B: Extend `currentSumStr` with `s[index]`. (This will lead to a new `currentSumStr` which might or might not be divisible by 3).
    // This implicitly means we are *not* taking the current `currentSumStr` as a final segment yet.
    // We want to maximize the segments. So should we even allow extending a already-divisible-by-3 segment?
    // Yes, because it might lead to more segments later on (though this specific segment might become invalid).
    // This makes the problem a bit more complex. Let's simplify and assume we want to maximize segments.
    // So if a segment is divisible by 3, we should take it.

    // Correct logic for the `else` block (when `index < |s|`):
    // Compare two scenarios:
    // 1. Extend the current `currentSumStr` by adding `s[index]`.
    var val_if_extend_current := MaxDivisibleBy3SegmentsHelper(s, index + 1, currentSumStr + s[index], count);

    // 2. Start a new segment with `s[index]`. In this case, we need to decide if the `currentSumStr` (before adding `s[index]`) was a valid segment.
    var new_count = count;
    if currentSumStr != "" && (currentSumStr as int) % 3 == 0 then
      new_count := count + 1;
    var val_if_start_new_segment := MaxDivisibleBy3SegmentsHelper(s, index + 1, "" + s[index], new_count);

    max(val_if_extend_current, val_if_start_new_segment)

  else // currentSumStr is empty or not divisible by 3
    // Option 1: Extend current segment
    var extend_val := MaxDivisibleBy3SegmentsHelper(s, index + 1, currentSumStr + s[index], count);
    
    // Option 2: Start a new segment
    var start_new_val := MaxDivisibleBy3SegmentsHelper(s, index + 1, "" + s[index], count); // 'count' doesn't change since currentSumStr wasn't valid

    max(extend_val, start_new_val)
}

function IntToString(n: int): string
  requires n >= 0
  ensures (n == 0) ==> (IntToString(n) == "0")
  ensures (n > 0) ==> (|IntToString(n)| > 0 && (IntToString(n) as int) == n)
{
  if n == 0 then "0"
  else
    var s := "";
    var temp := n;
    while temp > 0
      invariant temp >= 0
      invariant (s == "" || (s as int) >= 0)
      invariant (temp > 0 ==> (s as int) >= 0) // Ensure current s is a valid int if temp > 0
      invariant (n > 0 ==> (s == "" || (temp * (10_000_000_000_000_000_000:int)/*a large power of 10*/ + (s as int) == n)) // A bit tricky to formulate precisely
      invariant (n == (temp * (Pow10(|s|)) + (if s == "" then 0 else (s as int)))) // This invariant is hard to prove without Pow10
      decreases temp
    {
      s := (temp % 10 as char) + s;
      temp := temp / 10;
    }
    s
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures exists count :: 0 <= count <= |input|-1 && result == IntToString(count) + "\n"
    ensures exists count :: count == MaxDivisibleBy3Segments(input[0..|input|-1]) && result == IntToString(count) + "\n"
// </vc-spec>
// <vc-code>
{
  var trimmedInput := input[0..|input|-1]; // Remove the trailing newline
  var count := MaxDivisibleBy3Segments(trimmedInput);
  result := IntToString(count) + "\n";
}
// </vc-code>

