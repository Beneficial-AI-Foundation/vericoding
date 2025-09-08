Given a string of n digits where n is odd and n >= 13, two players (Vasya first, then Petya) 
take turns removing one character at a time until exactly 11 characters remain. 
Vasya wins if the final 11-character string starts with digit 8, otherwise Petya wins.
Determine if Vasya has a winning strategy.

predicate ValidInput(n: int, s: string)
{
    n >= 13 && n % 2 == 1 && |s| == n
}

function count_eights_in_prefix(s: string, len: int): int
    requires 0 <= len <= |s|
    ensures count_eights_in_prefix(s, len) >= 0
    ensures count_eights_in_prefix(s, len) <= len
{
    if len == 0 then 0
    else (if s[len-1] == '8' then 1 else 0) + count_eights_in_prefix(s, len-1)
}

predicate VasyaWins(n: int, s: string)
    requires ValidInput(n, s)
{
    var petya_moves := (n - 11) / 2;
    var prefix_len := n - 10;
    var eights_in_prefix := count_eights_in_prefix(s, prefix_len);
    petya_moves < eights_in_prefix
}

method solve(n: int, s: string) returns (result: string)
    requires ValidInput(n, s)
    ensures result == "NO" || result == "YES"
    ensures result == (if VasyaWins(n, s) then "YES" else "NO")
{
    var cnt := (n - 11) / 2;
    var prefix_len := n - 10;
    var cnt_8 := count_eights_in_prefix(s, prefix_len);

    if cnt >= cnt_8 {
        result := "NO";
    } else {
        result := "YES";
    }
}
