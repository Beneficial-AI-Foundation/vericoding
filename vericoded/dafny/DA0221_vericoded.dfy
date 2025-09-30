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

lemma count_all_directions(commands: string)
    requires ValidCommands(commands)
    ensures count_char(commands, 'L') + count_char(commands, 'R') + 
            count_char(commands, 'U') + count_char(commands, 'D') == |commands|
{
    if |commands| == 0 {
        // Base case
    } else {
        // Recursive case
        var c := commands[0];
        var rest := commands[1..];
        count_all_directions(rest);
        
        assert c in {'L', 'R', 'U', 'D'};
        
        if c == 'L' {
            assert count_char(commands, 'L') == 1 + count_char(rest, 'L');
            assert count_char(commands, 'R') == count_char(rest, 'R');
            assert count_char(commands, 'U') == count_char(rest, 'U');
            assert count_char(commands, 'D') == count_char(rest, 'D');
        } else if c == 'R' {
            assert count_char(commands, 'L') == count_char(rest, 'L');
            assert count_char(commands, 'R') == 1 + count_char(rest, 'R');
            assert count_char(commands, 'U') == count_char(rest, 'U');
            assert count_char(commands, 'D') == count_char(rest, 'D');
        } else if c == 'U' {
            assert count_char(commands, 'L') == count_char(rest, 'L');
            assert count_char(commands, 'R') == count_char(rest, 'R');
            assert count_char(commands, 'U') == 1 + count_char(rest, 'U');
            assert count_char(commands, 'D') == count_char(rest, 'D');
        } else {
            assert c == 'D';
            assert count_char(commands, 'L') == count_char(rest, 'L');
            assert count_char(commands, 'R') == count_char(rest, 'R');
            assert count_char(commands, 'U') == count_char(rest, 'U');
            assert count_char(commands, 'D') == 1 + count_char(rest, 'D');
        }
    }
}

lemma min_sum_bound(a: int, b: int, c: int, d: int, n: int)
    requires a >= 0 && b >= 0 && c >= 0 && d >= 0
    requires a + b + c + d == n
    ensures 2 * min(a, b) + 2 * min(c, d) <= n
{
    min_properties(a, b);
    min_properties(c, d);
    
    assert min(a, b) <= a && min(a, b) <= b;
    assert min(c, d) <= c && min(c, d) <= d;
    
    assert 2 * min(a, b) <= a + b;
    assert 2 * min(c, d) <= c + d;
    
    assert 2 * min(a, b) + 2 * min(c, d) <= a + b + c + d;
    assert a + b + c + d == n;
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
    
    count_all_directions(commands);
    assert countL + countR + countU + countD == n;
    
    var minLR := min(countL, countR);
    var minUD := min(countU, countD);
    
    min_properties(countL, countR);
    min_properties(countU, countD);
    
    result := 2 * minLR + 2 * minUD;
    
    min_sum_bound(countL, countR, countU, countD, n);
    
    assert result == 2 * min(count_char(commands, 'L'), count_char(commands, 'R')) + 
                     2 * min(count_char(commands, 'U'), count_char(commands, 'D'));
    assert result >= 0;
    assert result <= n;
    assert result % 2 == 0;
}
// </vc-code>

