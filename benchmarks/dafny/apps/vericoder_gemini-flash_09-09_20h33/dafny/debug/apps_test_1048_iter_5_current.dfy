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
function method count_char_upper_bound(s: string, c: char, n: int): bool
    reads s
    requires |s| == n
    ensures count_char(s, c) <= n
{
    count_char(s,c) <= n
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
    var L_count := count_char(commands, 'L');
    var R_count := count_char(commands, 'R');
    var U_count := count_char(commands, 'U');
    var D_count := count_char(commands, 'D');

    result := 2 * min(L_count, R_count) + 2 * min(U_count, D_count);
    assert result >= 0 by {
        assert L_count >= 0;
        assert R_count >= 0;
        assert U_count >= 0;
        assert D_count >= 0;
        calc {
            min(L_count, R_count);
            { assert L_count >= 0 && R_count >= 0; }
            _ >= 0;
        }
        calc {
            min(U_count, D_count);
            { assert U_count >= 0 && D_count >= 0; }
            _ >= 0;
        }
    }
    assert result <= n by {
        assert count_char_upper_bound(commands, 'L', n);
        assert count_char_upper_bound(commands, 'R', n);
        assert count_char_upper_bound(commands, 'U', n);
        assert count_char_upper_bound(commands, 'D', n);

        assert L_count <= n;
        assert R_count <= n;
        assert U_count <= n;
        assert D_count <= n;

        assert 2 * min(L_count, R_count) <= L_count + R_count;
        assert 2 * min(U_count, D_count) <= U_count + D_count;

        assert (L_count + R_count + U_count + D_count) == n by {
            var all_commands := count_char(commands, 'L') + count_char(commands, 'R') + count_char(commands, 'U') + count_char(commands, 'D');
            assert all_commands == n;
        }

        calc {
            result;
            2 * min(L_count, R_count) + 2 * min(U_count, D_count);
            _ <= (L_count + R_count) + (U_count + D_count);
            _ == L_count + R_count + U_count + D_count;
            _ == n;
        }
    }
    assert result % 2 == 0;
}
// </vc-code>

