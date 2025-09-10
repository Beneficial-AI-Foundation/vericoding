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
{
    find_char_from(s, c, 0)
}

function find_char_from(s: string, c: char, start: int): int
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == c then start
    else find_char_from(s, c, start + 1)
}

lemma find_char_properties(s: string, c: char)
    ensures var idx := find_char(s, c);
            (idx == -1 <==> c !in s) &&
            (idx >= 0 ==> 0 <= idx < |s| && s[idx] == c)
{
    find_char_from_properties(s, c, 0);
}

lemma find_char_from_properties(s: string, c: char, start: int)
    requires 0 <= start <= |s|
    ensures var idx := find_char_from(s, c, start);
            (idx == -1 <==> (forall i :: start <= i < |s| ==> s[i] != c)) &&
            (idx >= 0 ==> start <= idx < |s| && s[idx] == c)
    decreases |s| - start
{
    if start >= |s| {
    } else if s[start] == c {
    } else {
        find_char_from_properties(s, c, start + 1);
    }
}

lemma split_lines_properties(s: string)
    requires '\n' in s
    ensures var lines := split_lines(s);
            |lines| >= 1
{
    find_char_properties(s, '\n');
    var idx := find_char(s, '\n');
    assert idx >= 0;
    assert 0 <= idx < |s|;
    if idx < |s| && '\n' in s[idx+1..] {
        split_lines_properties(s[idx+1..]);
    }
}

lemma find_char_bounds(s: string, c: char)
    requires c in s
    ensures var idx := find_char(s, c);
            0 <= idx < |s|
{
    find_char_properties(s, c);
}

lemma split_lines_idx_bounds(s: string)
    requires '\n' in s
    ensures var idx := find_char(s, '\n');
            idx >= 0 && 0 <= idx < |s|
{
    find_char_properties(s, c);
    var idx := find_char(s, c);
    assert idx >= 0;
    assert idx < |s|;
}

lemma split_lines_slice_bounds(s: string)
    requires '\n' in s
    ensures var idx := find_char(s, '\n');
            idx >= 0 && 0 <= idx < |s| && idx + 1 <= |s|
{
    find_char_properties(s, '\n');
    var idx := find_char(s, '\n');
    assert idx >= 0;
    assert idx < |s|;
    assert idx + 1 <= |s|;
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
    find_char_properties(input, '\n');
    split_lines_slice_bounds(input);
    var lines := split_lines(input);
    
    if |lines| < 2 {
        result := "NO\n";
    } else {
        var digits_str := lines[1];
        var digits := string_to_digits(digits_str);
        
        if HasUniqueMovementSequence(digits) {
            result := "YES\n";
        } else {
            result := "NO\n";
        }
    }
}
// </vc-code>

