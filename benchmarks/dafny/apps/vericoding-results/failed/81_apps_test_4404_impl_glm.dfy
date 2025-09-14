predicate IsValidDateString(s: string, y: int, m: int, d: int)
{
    |s| >= 10 && 
    s[4] == '/' && s[7] == '/' &&
    StringToInt(s[0..4]) == y &&
    StringToInt(s[5..7]) == m &&
    StringToInt(s[8..10]) == d
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then CharToDigit(s[0])
    else if |s| == 2 then CharToDigit(s[0]) * 10 + CharToDigit(s[1])
    else if |s| == 4 then CharToDigit(s[0]) * 1000 + CharToDigit(s[1]) * 100 + CharToDigit(s[2]) * 10 + CharToDigit(s[3])
    else 0
}

function CharToDigit(c: char): int
{
    if '0' <= c <= '9' then (c as int) - ('0' as int) else 0
}

predicate ValidInput(s: string)
{
    exists y, m, d :: IsValidDateString(s, y, m, d) && y == 2019 && 1 <= m <= 12 && 1 <= d <= 31
}

predicate CorrectOutput(s: string, result: string)
{
    exists y, m, d :: IsValidDateString(s, y, m, d) && y == 2019 && 1 <= m <= 12 && 1 <= d <= 31 && 
    ((m < 4 || (m == 4 && d <= 30)) ==> result == "Heisei") && 
    ((m > 4 || (m == 4 && d > 30)) ==> result == "TBD")
}

// <vc-helpers>
lemma CorrectOutputImpliesAux(s: string)
    requires ValidInput(s)
    ensures CorrectOutput(s, 
        if s[5..7] == "01" || s[5..7] == "02" || s[5..7] == "03" 
        then "Heisei" 
        else if s[5..7] == "04" then (if s[8..10] <= "30" then "Heisei" else "TBD") 
        else "TBD")
{
    var y, m, d :| IsValidDateString(s, y, m, d) && y == 2019 && 1 <= m <= 12 && 1 <= d <= 31;
    if m == 1 || m == 2 || m == 3 {
        assert s[5..7] == if m==1 then "01" else if m==2 then "02" else "03";
        assert CorrectOutput(s, "Heisei");
        calc {
            if s[5..7] == "01" || s[5..7] == "02" || s[5..7] == "03" 
            then "Heisei" 
            else if s[5..7] == "04" then (if s[8..10] <= "30" then "Heisei" else "TBD") 
            else "TBD";
            "Heisei";
        }
    } else if m == 4 {
        assert s[5..7] == "04";
        if d <= 30 {
            assert s[8..10] <= "30";
            assert CorrectOutput(s, "Heisei");
            calc {
                if s[5..7] == "01" || s[5..7] == "02" || s[5..7] == "03" 
                then "Heisei" 
                else if s[5..7] == "04" then (if s[8..10] <= "30" then "Heisei" else "TBD") 
                else "TBD";
                "Heisei";
            }
        } else {
            assert d == 31;
            assert s[8..10] == "31";
            assert "31" > "30";
            assert s[8..10] > "30";
            assert CorrectOutput(s, "TBD");
            calc {
                if s[5..7] == "01" || s[5..7] == "02" || s[5..7] == "03" 
                then "Heisei" 
                else if s[5..7] == "04" then (if s[8..10] <= "30" then "Heisei" else "TBD") 
                else "TBD";
                "TBD";
            }
        }
    } else {
        assert m>=5 && m<=12;
        assert s[5..7] != "01" && s[5..7] != "02" && s[5..7] != "03" && s[5..7] != "04";
        assert CorrectOutput(s, "TBD");
        calc {
            if s[5..7] == "01" || s[5..7] == "02" || s[5..7] == "03" 
            then "Heisei" 
            else if s[5..7] == "04" then (if s[8..10] <= "30" then "Heisei" else "TBD") 
            else "TBD";
            "TBD";
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
requires |stdin_input| > 0
requires ValidInput(stdin_input)
ensures CorrectOutput(stdin_input, result)
// </vc-spec>
// <vc-code>
{
    CorrectOutputImpliesAux(stdin_input);
    result := if stdin_input[5..7] == "01" || stdin_input[5..7] == "02" || stdin_input[5..7] == "03" 
             then "Heisei" 
             else if stdin_input[5..7] == "04" then (if stdin_input[8..10] <= "30" then "Heisei" else "TBD") 
             else "TBD";
}
// </vc-code>

