// <vc-preamble>
predicate validInput(input: string)
{
  var lines := splitLines(input);
  |lines| >= 3 &&
  parseInt(lines[0]) > 0 &&
  |lines[1]| == parseInt(lines[0]) &&
  |lines[2]| == parseInt(lines[0]) &&
  (forall c :: c in lines[1] ==> 'a' <= c <= 'z') &&
  (forall c :: c in lines[2] ==> 'a' <= c <= 'z')
}

function extractWords(input: string): (string, string)
  requires validInput(input)
  ensures extractWords(input).0 == splitLines(input)[1]
  ensures extractWords(input).1 == splitLines(input)[2]
  ensures |extractWords(input).0| == |extractWords(input).1| > 0
{
  var lines := splitLines(input);
  (lines[1], lines[2])
}

function computeMinPreprocessingMoves(word1: string, word2: string): int
  requires |word1| == |word2| > 0
  ensures computeMinPreprocessingMoves(word1, word2) >= 0
  ensures computeMinPreprocessingMoves(word1, word2) <= |word1|
  ensures |word1| == 1 ==> computeMinPreprocessingMoves(word1, word2) == (if word1[0] == word2[0] then 0 else 1)
  ensures computeMinPreprocessingMoves(word1, word2) == sumPositionGroupContributions(word1, word2)
{
  sumPositionGroupContributions(word1, word2)
}

function intToString(i: int): string
  requires i >= 0
  ensures |intToString(i)| > 0
  ensures forall c :: c in intToString(i) ==> c in "0123456789"
  ensures i == 0 ==> intToString(i) == "0"
  ensures i == 1 ==> intToString(i) == "1"
{
  if i == 0 then "0"
  else if i == 1 then "1"
  else if i == 2 then "2"
  else if i == 3 then "3"
  else if i == 4 then "4"
  else if i == 5 then "5"
  else if i == 6 then "6"
  else if i == 7 then "7"
  else if i == 8 then "8"
  else if i == 9 then "9"
  else if i == 10 then "10"
  else "0"
}
// </vc-preamble>

// <vc-helpers>
function splitLines(input: string): seq<string>
  ensures |splitLines(input)| >= 0
  ensures forall line :: line in splitLines(input) ==> '\n' !in line
{
  splitLinesHelper(input, 0, "", [])
}

function splitLinesHelper(input: string, index: int, current: string, lines: seq<string>): seq<string>
  requires 0 <= index <= |input|
  requires '\n' !in current
  requires forall line :: line in lines ==> '\n' !in line
  ensures forall line :: line in splitLinesHelper(input, index, current, lines) ==> '\n' !in line
  decreases |input| - index
{
  if index == |input| then
    if current == "" then lines else lines + [current]
  else if input[index] == '\n' then
    splitLinesHelper(input, index + 1, "", lines + [current])
  else
    splitLinesHelper(input, index + 1, current + [input[index]], lines)
}

function parseInt(s: string): int
  ensures parseInt(s) >= 0
  ensures s == "0" ==> parseInt(s) == 0
  ensures s == "1" ==> parseInt(s) == 1
{
  if s == "0" then 0
  else if s == "1" then 1
  else if s == "2" then 2
  else if s == "3" then 3
  else if s == "4" then 4
  else if s == "5" then 5
  else if s == "6" then 6
  else if s == "7" then 7
  else if s == "8" then 8
  else if s == "9" then 9
  else if s == "10" then 10
  else 0
}

function sumPositionGroupContributions(word1: string, word2: string): int
  requires |word1| == |word2| > 0
  ensures sumPositionGroupContributions(word1, word2) >= 0
  ensures sumPositionGroupContributions(word1, word2) <= |word1|
{
  sumOfContributions(word1, word2, (|word1| + 1) / 2)
}

function sumOfContributions(word1: string, word2: string, upTo: int): int
  requires |word1| == |word2| >= 1
  requires 0 <= upTo <= (|word1| + 1) / 2
  ensures sumOfContributions(word1, word2, upTo) >= 0
  ensures sumOfContributions(word1, word2, upTo) <= upTo * 2
  decreases upTo
{
  if upTo == 0 then 0
  else sumOfContributions(word1, word2, upTo - 1) + positionGroupContribution(word1, word2, upTo - 1)
}

function positionGroupContribution(word1: string, word2: string, i: int): int
  requires |word1| == |word2| > 0
  requires 0 <= i < |word1|
  requires 0 <= |word1| - 1 - i < |word1|
  ensures positionGroupContribution(word1, word2, i) >= 0
  ensures positionGroupContribution(word1, word2, i) <= 2
{
  if i == |word1| - 1 - i then
    if word1[i] == word2[i] then 0 else 1
  else
    var chars := [word1[i], word1[|word1| - 1 - i], word2[i], word2[|word1| - 1 - i]];
    var uniqueCount := |setFromSeq(chars)|;
    if uniqueCount == 4 then 2
    else if uniqueCount == 3 then
      if word1[i] == word1[|word1| - 1 - i] then 2 else 1
    else if uniqueCount == 2 then
      var firstChar := chars[0];
      var firstCharCount := countOccurrences(chars, firstChar);
      if firstCharCount != 2 then 1 else 0
    else 0
}

function setFromSeq(s: seq<char>): set<char>
  ensures forall x :: x in setFromSeq(s) <==> x in s
{
  set x | x in s
}

function countOccurrences(s: seq<char>, target: char): int
  ensures countOccurrences(s, target) >= 0
  ensures countOccurrences(s, target) <= |s|
  decreases |s|
{
  if |s| == 0 then 0
  else if s[0] == target then 1 + countOccurrences(s[1..], target)
  else countOccurrences(s[1..], target)
}

lemma UniqueSeqBounds(s: seq<char>)
  requires |s| > 0
  ensures |setFromSeq(s)| >= 1
  ensures |setFromSeq(s)| <= |s|
{
  var uniqueSet := setFromSeq(s);
  assert s[0] in uniqueSet;
  SetCardinalityBound(s);
}

lemma SetCardinalityBound<T>(s: seq<T>)
  ensures |set x | x in s| <= |s|
{
  if |s| == 0 {
  } else {
    var tail := s[1..];
    SetCardinalityBound(tail);
    var tailSet := set x | x in tail;
    var fullSet := set x | x in s;
    assert fullSet == tailSet + {s[0]};
    if s[0] in tailSet {
      assert fullSet == tailSet;
      assert |fullSet| == |tailSet|;
    } else {
      assert |fullSet| == |tailSet| + 1;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires |stdin_input| > 0
  requires validInput(stdin_input)
  ensures result == intToString(computeMinPreprocessingMoves(extractWords(stdin_input).0, extractWords(stdin_input).1)) + "\n"
  ensures |result| > 0
  ensures result[|result|-1] == '\n'
  ensures forall c :: c in result[..|result|-1] ==> c in "0123456789"
// </vc-spec>
// <vc-code>
{
  var lines := splitLines(stdin_input);
  if |lines| < 3 {
    result := "0\n";
    return;
  }

  var n := parseInt(lines[0]);
  if n <= 0 || |lines[1]| != n || |lines[2]| != n {
    result := "0\n";
    return;
  }

  var word1 := lines[1];
  var word2 := lines[2];

  var count := computeMinPreprocessingMoves(word1, word2);
  result := intToString(count) + "\n";
}
// </vc-code>
