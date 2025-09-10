function is_tandem_repeat(s: seq<char>): bool
{
    if |s| % 2 != 0 then false
    else
        var half_len := |s| / 2;
        var first_half := s[0..half_len];
        var second_half := s[half_len..];
        forall i :: 0 <= i < half_len ==> 
            (first_half[i] == '*' || second_half[i] == '*' || first_half[i] == second_half[i])
}

// <vc-helpers>
function IsTandemRepeatWithK(s: seq<char>, k: int, start: int, len: int): bool
    requires len % 2 == 0
    requires len >= 2
    requires start >= 0
    requires start + len <= |s| + k
{
    var half_len := len / 2;
    var s_prime := s + seq(k, _ => '*');
    forall i :: 0 <= i < half_len ==>
        (s_prime[start + i] == '*' || s_prime[start + half_len + i] == '*' || s_prime[start + i] == s_prime[start + half_len + i])
}
// </vc-helpers>

// <vc-spec>
method solve(s: string, k: int) returns (result: int)
    requires k >= 1
    requires |s| >= 1
    ensures result >= 0
    ensures result % 2 == 0
    ensures result <= |s| + k
    ensures forall i, n :: 0 <= i < |s| + k && 2 <= n <= |s| + k - i && n % 2 == 0 && 
            is_tandem_repeat((s + seq(k, j => '*'))[i..i+n]) ==> n <= result
    ensures result == 0 ==> forall i, n :: 0 <= i < |s| + k && 2 <= n <= |s| + k - i && n % 2 == 0 ==> 
            !is_tandem_repeat((s + seq(k, j => '*'))[i..i+n])
    ensures result > 0 ==> exists i, n :: 0 <= i < |s| + k && 2 <= n <= |s| + k - i && n % 2 == 0 && 
            (is_tandem_repeat((s + seq(k, j => '*'))[i..i+n]) && n == result)
// </vc-spec>
// <vc-code>
{
    var max_tandem_repeat_len: int := 0;
    var s_extended := s + seq(k, _ => '*');

    // Iterate over all possible start positions
    for i := 0 to |s_extended|
        invariant 0 <= i <= |s_extended|
        invariant max_tandem_repeat_len % 2 == 0
        invariant forall current_i, current_n :: 0 <= current_i < i && 2 <= current_n <= |s_extended| - current_i && current_n % 2 == 0 && is_tandem_repeat(s_extended[current_i .. current_i + current_n]) ==> current_n <= max_tandem_repeat_len
    {
        // Iterate over all possible even lengths starting from 2
        for n := 2 to (|s_extended| - i) by 2
            invariant 0 <= i < |s_extended|
            invariant 2 <= n <= |s_extended| - i + 1
            invariant n % 2 == 0
            invariant max_tandem_repeat_len % 2 == 0
            invariant forall current_n_inner :: 2 <= current_n_inner < n && current_n_inner % 2 == 0 && is_tandem_repeat(s_extended[i .. i + current_n_inner]) ==> current_n_inner <= max_tandem_repeat_len
        {
            if is_tandem_repeat(s_extended[i..i+n]) {
                if n > max_tandem_repeat_len {
                    max_tandem_repeat_len := n;
                }
            }
        }
    }
    return max_tandem_repeat_len;
}
// </vc-code>

