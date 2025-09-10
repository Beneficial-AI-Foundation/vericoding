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
  decreases s
{
  if |s| == 0 then -1
  else if s[0] == c then 0
  else
    var rest_find := find_char(s[1..], c);
    if rest_find == -1 then -1 else 1 + rest_find
}

lemma find_char_props(s: string, c: char)
  ensures '\n' in s ==> find_char(s, '\n') >= 0
  ensures find_char(s, c) == -1 ==> c !in s
  ensures 0 <= find_char(s, c) < |s| ==> s[find_char(s, c)] == c
{
}

lemma split_lines_has_newline(s: string)
  requires '\n' in s
  ensures |split_lines(s)| >= 2
{
}

lemma split_lines_props(s: string)
  ensures |split_lines(s)| > 0
  ensures forall i :: 0 <= i < |split_lines(s)| ==> |split_lines(s)[i]| >= 0
{
}

lemma string_to_digits_empty(s: string)
  requires |s| == 0
  ensures string_to_digits(s) == {}
{
}

lemma string_to_digits_nonempty(s: string)
  requires |s| > 0
  ensures string_to_digits(s) == set i | 0 <= i < |s| && '0' <= s[i] <= '9' :: (s[i] as int) - ('0' as int)
{
}

lemma HasUniqueMovementSequence_definition(digits: set<int>)
  ensures HasUniqueMovementSequence(digits) == (
    (1 in digits || 4 in digits || 7 in digits || 0 in digits) &&
    (1 in digits || 2 in digits || 3 in digits) &&
    (3 in digits || 6 in digits || 9 in digits || 0 in digits) &&
    (7 in digits || 0 in digits || 9 in digits)
  )
{
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
  if |lines| < 2 {
    result := "YES\n";
  } else {
    var digits_str := lines[1];
    var digits := string_to_digits(digits_str);
    
    if (1 in digits || 4 in digits || 7 in digits || 0 in digits) &&
       (1 in digits || 2 in digits || 3 in digits) &&
       (3 in digits || 6 in digits || 9 in digits || 0 in digits) &&
       (7 in digits || 0 in digits || 9 in digits) {
      result := "YES\n";
    } else {
      result := "NO\n";
    }
  }
}
// </vc-code>

