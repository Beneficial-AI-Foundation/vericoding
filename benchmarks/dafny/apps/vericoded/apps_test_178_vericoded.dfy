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

// <vc-helpers>
method count_eights_iterative(s: string, len: int) returns (count: int)
    requires 0 <= len <= |s|
    ensures count == count_eights_in_prefix(s, len)
{
    count := 0;
    var i := 0;
    
    while i < len
        invariant 0 <= i <= len
        invariant count == count_eights_in_prefix(s, i)
    {
        if s[i] == '8' {
            count := count + 1;
        }
        i := i + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (result: string)
    requires ValidInput(n, s)
    ensures result == "NO" || result == "YES"
    ensures result == (if VasyaWins(n, s) then "YES" else "NO")
// </vc-spec>
// <vc-code>
{
    var petya_moves := (n - 11) / 2;
    var prefix_len := n - 10;
    var eights_in_prefix := count_eights_iterative(s, prefix_len);
    
    if petya_moves < eights_in_prefix {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

