function string_to_digits(s: string): set<int>
{
    set i | 0 <= i < |s| && '0' <= s[i] <= '9' :: (s[i] as int) - ('0' as int)
}

predicate ValidInput(input: string)
{
    |input| > 0 && '\n' in input
}

predicate HasUniqueMovementSequence(digits: set<int>)
{
    (1 in digits || 4 in digits || 7 in digits || 0 in digits) &&
    (1 in digits || 2 in digits || 3 in digits) &&
    (3 in digits || 6 in digits || 9 in digits || 0 in digits) &&
    (7 in digits || 0 in digits || 9 in digits)
}

function split_lines(s: string): seq<string>
{
    if '\n' !in s then [s]
    else 
        var idx := find_char(s, '\n');
        if idx == -1 then [s]
        else if idx < |s| then [s[..idx]] + split_lines(s[idx+1..])
        else [s]
}

// <vc-helpers>
function find_char(s: string, c: char): int
  decreases |s|
{
  if |s| == 0 then -1
  else if s[0] == c then 0
  else 
    var idx := find_char(s[1..], c);
    if idx == -1 then -1 else idx+1
}

lemma SplitLinesNonEmpty(s: string)
  ensures |split_lines(s)| >= 1
  decreases |s|
{
  if '\n' !in s {
  } else {
    var idx := find_char(s, '\n');
    if idx == -1 {
    } else if idx < |s| {
      SplitLinesNonEmpty(s[idx+1..]);
    } else {
    }
  }
}

lemma ValidInputImpliesAtLeastTwoLines(input: string)
  requires ValidInput(input)
  ensures |split_lines(input)| >= 2
{
  var idx := find_char(input, '\n');
  assert split_lines(input) == [input[..idx]] + split_lines(input[idx+1..]);
  SplitLinesNonEmpty(input[idx+1..]);
  assert |split_lines(input)| == 1 + |split_lines(input[idx+1..])|;
  assert |split_lines(input)| >= 2;
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
  requires ValidInput(input)
  ensures result == "YES\n" || result == "NO\n"
  ensures |result| > 0
  ensures var lines := split_lines(input);
          |lines| >= 2 ==>
          var digits_str := lines[1];
          var digits := string_to_digits(digits_str);
          result == "YES\n" <==> HasUniqueMovementSequence(digits)
// </vc-spec>
// <vc-code>
{
  var lines := split_lines(input);
  ValidInputImpliesAtLeastTwoLines(input);
  assert |lines| >= 2;
  var digits_str := lines[1];
  var digits := string_to_digits(digits_str);
  if HasUniqueMovementSequence(digits) {
      return "YES\n";
  } else {
      return "NO\n";
  }
}
// </vc-code>

