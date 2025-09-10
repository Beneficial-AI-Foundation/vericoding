function count_char(s: string, c: char): int
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + count_char(s[1..], c)
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

predicate ValidCommands(commands: string)
{
    forall i :: 0 <= i < |commands| ==> commands[i] in {'L', 'R', 'U', 'D'}
}

// <vc-helpers>
lemma count_char_non_negative(s: string, c: char)
    ensures count_char(s, c) >= 0
{
    if |s| == 0 {
        // Base case: empty string has count 0
    } else {
        // Recursive case
        count_char_non_negative(s[1..], c);
    }
}

lemma count_char_bounded(s: string, c: char)
    ensures count_char(s, c) <= |s|
{
    if |s| == 0 {
        // Base case: empty string
    } else {
        // Recursive case
        count_char_bounded(s[1..], c);
        assert count_char(s[1..], c) <= |s[1..]|;
        assert |s[1..]| == |s| - 1;
    }
}

lemma min_properties(a: int, b: int)
    ensures min(a, b) <= a
    ensures min(a, b) <= b
    ensures min(a, b) == a || min(a, b) == b
{
    // Follows directly from definition
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, commands: string) returns (result: int)
    requires n >= 0
    requires |commands| == n
    requires ValidCommands(commands)
    ensures result >= 0
    ensures result <= n
    ensures result % 2 == 0
    ensures result == 2 * min(count_char(commands, 'L'), count_char(commands, 'R')) + 
                     2 * min(count_char(commands, 'U'), count_char(commands, 'D'))
// </vc-spec>
// <vc-code>
{
    var countL := count_char(commands, 'L');
    var countR := count_char(commands, 'R');
    var countU := count_char(commands, 'U');
    var countD := count_char(commands, 'D');
    
    count_char_non_negative(commands, 'L');
    count_char_non_negative(commands, 'R');
    count_char_non_negative(commands, 'U');
    count_char_non_negative(commands, 'D');
    
    count_char_bounded(commands, 'L');
    count_char_bounded(commands, 'R');
    count_char_bounded(commands, 'U');
    count_char_bounded(commands, 'D');
    
    var minLR := min(countL, countR);
    var minUD := min(countU, countD);
    
    min_properties(countL, countR);
    min_properties(countU, countD);
    
    result := 2 * minLR + 2 * minUD;
    
    assert result == 2 * min(count_char(commands, 'L'), count_char(commands, 'R')) + 
                     2 * min(count_char(commands, 'U'), count_char(commands, 'D'));
    assert result >= 0;
    assert minLR <= n && minUD <= n;
    assert result <= 2 * n;
    assert result <= n || n == 0 || result == 2 * n;
    assert result % 2 == 0;
}
// </vc-code>

