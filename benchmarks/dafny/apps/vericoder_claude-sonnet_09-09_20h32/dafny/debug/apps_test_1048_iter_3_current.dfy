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
lemma CountCharNonNegative(s: string, c: char)
    ensures count_char(s, c) >= 0
{
    if |s| == 0 {
    } else {
        CountCharNonNegative(s[1..], c);
    }
}

lemma CountCharBounded(s: string, c: char)
    ensures count_char(s, c) <= |s|
{
    if |s| == 0 {
    } else {
        CountCharBounded(s[1..], c);
    }
}

lemma MinProperties(a: int, b: int)
    ensures min(a, b) <= a
    ensures min(a, b) <= b
    ensures min(a, b) >= 0 ==> a >= 0 || b >= 0
{
}

lemma CountCharSum(s: string)
    requires ValidCommands(s)
    ensures count_char(s, 'L') + count_char(s, 'R') + count_char(s, 'U') + count_char(s, 'D') == |s|
{
    if |s| == 0 {
    } else {
        CountCharSum(s[1..]);
    }
}

lemma MinBoundHelper(a: int, b: int, total: int)
    requires a >= 0 && b >= 0 && a <= total && b <= total
    ensures 2 * min(a, b) <= total
{
    if total >= 2 {
        if a <= b {
            assert min(a, b) == a;
            assert a <= total;
            if a <= total / 2 {
                assert 2 * a <= total;
            }
        } else {
            assert min(a, b) == b;
            assert b <= total;
            if b <= total / 2 {
                assert 2 * b <= total;
            }
        }
    }
}

lemma ResultBound(commands: string, n: int)
    requires n >= 0
    requires |commands| == n
    requires ValidCommands(commands)
    ensures 2 * min(count_char(commands, 'L'), count_char(commands, 'R')) + 
            2 * min(count_char(commands, 'U'), count_char(commands, 'D')) <= n
{
    CountCharBounded(commands, 'L');
    CountCharBounded(commands, 'R');
    CountCharBounded(commands, 'U');
    CountCharBounded(commands, 'D');
    CountCharNonNegative(commands, 'L');
    CountCharNonNegative(commands, 'R');
    CountCharNonNegative(commands, 'U');
    CountCharNonNegative(commands, 'D');
    
    var lr_sum := count_char(commands, 'L') + count_char(commands, 'R');
    var ud_sum := count_char(commands, 'U') + count_char(commands, 'D');
    
    assert lr_sum + ud_sum <= n by {
        CountCharSum(commands);
    }
    
    assert 2 * min(count_char(commands, 'L'), count_char(commands, 'R')) <= lr_sum;
    assert 2 * min(count_char(commands, 'U'), count_char(commands, 'D')) <= ud_sum;
    assert 2 * min(count_char(commands, 'L'), count_char(commands, 'R')) + 
           2 * min(count_char(commands, 'U'), count_char(commands, 'D')) <= lr_sum + ud_sum;
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
    
    CountCharNonNegative(commands, 'L');
    CountCharNonNegative(commands, 'R');
    CountCharNonNegative(commands, 'U');
    CountCharNonNegative(commands, 'D');
    
    CountCharBounded(commands, 'L');
    CountCharBounded(commands, 'R');
    CountCharBounded(commands, 'U');
    CountCharBounded(commands, 'D');
    
    CountCharSum(commands);
    
    var minLR := min(countL, countR);
    var minUD := min(countU, countD);
    
    MinProperties(countL, countR);
    MinProperties(countU, countD);
    
    ResultBound(commands, n);
    
    result := 2 * minLR + 2 * minUD;
}
// </vc-code>

