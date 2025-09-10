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
lemma count_eights_in_prefix_monotonic(s: string, a: int, b: int)
    requires 0 <= a <= b <= |s|
    ensures count_eights_in_prefix(s, a) <= count_eights_in_prefix(s, b)
{
    if a < b {
        count_eights_in_prefix_monotonic(s, a, b - 1);
    }
}

lemma count_eights_in_prefix_suffix(s: string, len: int, add: int)
    requires 0 <= len <= |s| && 0 <= add <= |s| - len
    ensures count_eights_in_prefix(s, len + add) == 
           count_eights_in_prefix(s, len) + 
           count_eights_in_prefix(s[len..], add)
{
    if add > 0 {
        count_eights_in_prefix_suffix(s, len, add - 1);
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
    var eights_in_prefix := count_eights_in_prefix(s, prefix_len);
    
    if petya_moves < eights_in_prefix {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

