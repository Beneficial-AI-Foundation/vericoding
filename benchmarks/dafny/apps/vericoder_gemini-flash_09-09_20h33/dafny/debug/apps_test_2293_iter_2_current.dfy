predicate ValidInput(input: string)
{
    |input| > 0 && input[|input|-1] == '\n' &&
    var lines := SplitByNewlines(input);
    |lines| >= 2 && 
    var firstLineParts := SplitBySpaces(lines[0]);
    |firstLineParts| >= 2 &&
    var m := StringToInt(firstLineParts[0]);
    var n := StringToInt(firstLineParts[1]);
    m >= 1 && n >= 1 && m + 1 < |lines| &&
    forall dayIdx :: 1 <= dayIdx <= m ==> 
        var dayLine := SplitBySpaces(lines[dayIdx]);
        |dayLine| >= 1 &&
        var s := StringToInt(dayLine[0]);
        s >= 1 && s < n && s + 1 <= |dayLine| &&
        forall storeIdx :: 1 <= storeIdx <= s ==> 
            var store := StringToInt(dayLine[storeIdx]);
            1 <= store <= n
}

function ExtractDoraSet(input: string, dayIndex: int, n: int): set<int>
    requires |input| > 0
    requires dayIndex >= 0
    requires n >= 1
{
    var lines := SplitByNewlines(input);
    if dayIndex + 1 >= |lines| then {}
    else
        var dayLine := SplitBySpaces(lines[dayIndex + 1]);
        if |dayLine| <= 1 then {}
        else
            var s := StringToInt(dayLine[0]);
            if s + 1 > |dayLine| then {}
            else
                set storeIdx | 1 <= storeIdx <= s && storeIdx < |dayLine| :: StringToInt(dayLine[storeIdx])
}

function ExtractSwiperSet(input: string, dayIndex: int, n: int): set<int>
    requires |input| > 0
    requires dayIndex >= 0
    requires n >= 1
{
    var allStores := set i {:trigger} | 1 <= i <= n :: i;
    var doraSet := ExtractDoraSet(input, dayIndex, n);
    allStores - doraSet
}

predicate SolutionExists(input: string)
    requires ValidInput(input)
{
    var lines := SplitByNewlines(input);
    var firstLineParts := SplitBySpaces(lines[0]);
    var m := StringToInt(firstLineParts[0]);
    var n := StringToInt(firstLineParts[1]);
    forall i, j :: 0 <= i < m && 0 <= j < m ==> 
        !(ExtractDoraSet(input, i, n) <= ExtractSwiperSet(input, j, n))
}

// <vc-helpers>
function SplitByNewlines(s: string): seq<string>
  ensures forall i :: 0 <= i < |SplitByNewlines(s)| ==> |SplitByNewlines(s)[i]| >= 0
{
  if s == "" then []
  else
    var i := 0;
    while i < |s| && s[i] != '\n'
      invariant 0 <= i <= |s|
      decreases |s| - i
    {
      i := i + 1;
    }
    if i < |s| then
      [s[..i]] + SplitByNewlines(s[i+1..])
    else
      [s]
}

function SplitBySpaces(s: string): seq<string>
  ensures forall i :: 0 <= i < |SplitBySpaces(s)| ==> |SplitBySpaces(s)[i]| >= 0
{
  if s == "" then []
  else
    var i := 0;
    while i < |s| && s[i] != ' '
      invariant 0 <= i <= |s|
      decreases |s| - i
    {
      i := i + 1;
    }
    if i < |s| then
      [s[..i]] + SplitBySpaces(s[i+1..])
    else
      [s]
}

function StringToInt(s: string): int
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  requires |s| > 0
  ensures StringToInt(s) >= 0
{
  if |s| == 1 then
    (s[0] as int) - ('0' as int)
  else
    (StringToInt(s[..|s|-1]) * 10) + ((s[|s|-1] as int) - ('0' as int))
}

// Function to check if a solution exists based on the problem logic.
// This function is a direct translation of the SolutionExists predicate.
function DoesSolutionExist(input: string): bool
    requires ValidInput(input)
{
    var lines := SplitByNewlines(input);
    var firstLineParts := SplitBySpaces(lines[0]);
    var m := StringToInt(firstLineParts[0]);
    var n := StringToInt(firstLineParts[1]);

    // Construct the actual parameters for the loop and forall
    var extractedDoraSets: seq<set<int>> := [];
    var extractedSwiperSets: seq<set<int>> := [];

    // Fill the sequences for Dora and Swiper sets.
    var k := 0;
    while k < m
        invariant 0 <= k <= m
        invariant |extractedDoraSets| == k
        invariant |extractedSwiperSets| == k
    {
        extractedDoraSets := extractedDoraSets + [ExtractDoraSet(input, k, n)];
        extractedSwiperSets := extractedSwiperSets + [ExtractSwiperSet(input, k, n)];
        k := k + 1;
    }

    // Check the condition from SolutionExists predicate using the pre-calculated sets.
    // This allows for explicit iteration in the code section.
    forall i, j :: 0 <= i < m && 0 <= j < m ==> 
        !(extractedDoraSets[i] <= extractedSwiperSets[j])
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == "possible" || result == "impossible"
    ensures result == "possible" <==> SolutionExists(input)
// </vc-spec>
// <vc-code>
{
    if DoesSolutionExist(input) then
        result := "possible"
    else
        result := "impossible";
}
// </vc-code>

